#include "HashOpaquePass.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <random>
#include <string>
#include <unordered_set>
#include <vector>

using namespace llvm;

llvm::cl::opt<bool> HashOpaqueEnable("obfhashopq", llvm::cl::init(true), llvm::cl::desc("Uses Existing Hash Trees To Create Opaque Branches, As well as interjecting always false hashes on runtime values"));

static constexpr unsigned Mode1FanoutMin = 10;
static constexpr unsigned Mode1FanoutMax = 24;
static constexpr unsigned Mode1DonorCloneCap = 6;
static constexpr unsigned Mode1PerFunctionCap = 32;

static constexpr unsigned Mode2PerFunctionCap = 16;
static constexpr unsigned Mode2MinBBInsts = 2;
static constexpr unsigned Mode2FanoutMin = 6;
static constexpr unsigned Mode2FanoutMax = 16;
static constexpr unsigned Mode2DonorCloneCap = 4;

static constexpr unsigned AuxCountMin = 2;
static constexpr unsigned AuxCountMax = 3;

static constexpr unsigned DecoyMinTailOps = 2;
static constexpr unsigned DecoyMaxTailOps = 6;
static constexpr unsigned DecoyStoreChancePct = 10;

static constexpr bool SkipLoopsMode2 = false;
static constexpr bool SkipEntryMode2 = false;

static constexpr unsigned StealCeiling = 16;
static constexpr unsigned StealFloor = 4;
static constexpr unsigned RealBBMinResidue = 5;

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;
        if (strcmp(cds->getAsString().str().c_str(), tag) == 0) return true;
    }
    return false;
}

static bool HasObfuscateAnnotation(Function& f) { return HasAnnotationTag(f, "obfus"); }
static bool HasNoObfuscateAnnotation(Function& f) { return HasAnnotationTag(f, "noobfus"); }
static bool HasNoHashOpaqueAnnotation(Function& f) { return HasAnnotationTag(f, "nohashopq"); }

static std::mt19937_64 Rng;


static GlobalVariable* HashSaltGV = nullptr;

static void EnsureHashSalt(Module& m)
{
    if (HashSaltGV) return;
    LLVMContext& c = m.getContext();
    IntegerType* i64 = Type::getInt64Ty(c);

    HashSaltGV = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, 0), ".HashopqSalt");
    HashSaltGV->setUnnamedAddr(GlobalValue::UnnamedAddr::None);
    HashSaltGV->setAlignment(Align(8));

    FunctionType* ft = FunctionType::get(Type::getVoidTy(c), false);
    Function* saltinit = Function::Create(ft, GlobalValue::InternalLinkage, "HashopqSaltInit", &m);
    saltinit->addFnAttr(Attribute::NoInline);
    BasicBlock* entry = BasicBlock::Create(c, "Entry", saltinit);
    IRBuilder<> ib(entry);

    // tsc store MUST be volatile so LLVM can't propagate the readcyclecounter result through the ctor into use sites; a none volatile store lets GVN fold the salt reads to a constant and collapses the per run variance the whole design depends on
    Function* rdtsc = Intrinsic::getDeclaration(&m, Intrinsic::readcyclecounter);
    Value* tsc = ib.CreateCall(rdtsc, {}, "HashopqRdtsc");
    StoreInst* st = ib.CreateStore(tsc, HashSaltGV);
    st->setVolatile(true);
    st->setAlignment(Align(8));
    ib.CreateRetVoid();

    appendToGlobalCtors(m, saltinit, 102);
}

static bool BBAlreadyProcessedMode2(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    return term && term->getMetadata("hashopq.m2_done") != nullptr;
}

static void MarkBBProcessedMode2(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    if (!term) return;
    term->setMetadata("hashopq.m2_done", MDNode::get(bb->getContext(), {}));
}

static bool SiteAlreadyRewritten(Instruction* i)
{
    return i && i->getMetadata("hashopq.m1_done") != nullptr;
}

static void MarkSiteRewritten(Instruction* i)
{
    if (!i) return;
    i->setMetadata("hashopq.m1_done", MDNode::get(i->getContext(), {}));
}

static bool IsDecoyBlock(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    return term && term->getMetadata("hashopq.decoy") != nullptr;
}

static void MarkDecoyBlock(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    if (!term) return;
    term->setMetadata("hashopq.decoy", MDNode::get(bb->getContext(), {}));
}

static void TagEscalateConstMBA(Value* v)
{
    auto* inst = dyn_cast<Instruction>(v);
    if (!inst) return;
    LLVMContext& c = inst->getContext();
    Metadata* ops[1] = { MDString::get(c, "poly_const") };
    inst->setMetadata("mbagen.escalate", MDNode::get(c, ops));
}

static Value* InsertFoldBarrier(IRBuilder<>& b, Value* v)
{
    Type* ty = v->getType();
    if (!ty->isIntegerTy()) return v;
    FunctionType* asmty = FunctionType::get(ty, { ty }, false);
    InlineAsm* ia = InlineAsm::get(asmty, "", "=r,0", true);
    return b.CreateCall(ia, { v }, "HashopqBarrier");
}

static GlobalVariable* GetOrCreateHashOpaqueSink(Module& m)
{
    const char* name = ".HashopqSink";
    if (auto* existing = m.getGlobalVariable(name)) return existing;
    LLVMContext& c = m.getContext();
    IntegerType* i64 = Type::getInt64Ty(c);
    auto* gv = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, 0), name);
    gv->setUnnamedAddr(GlobalValue::UnnamedAddr::None);
    gv->setAlignment(Align(8));
    return gv;
}

static Value* EmitSinkLoad(IRBuilder<>& b, Module& m, IntegerType* i64, const char* name)
{
    GlobalVariable* sink = GetOrCreateHashOpaqueSink(m);
    LoadInst* ld = b.CreateLoad(i64, sink, true, name);
    ld->setAlignment(Align(8));
    return ld;
}

static Instruction* PickInsertionPointMode2(BasicBlock* bb, std::mt19937_64& rng)
{
    Instruction* first = bb->getFirstNonPHIOrDbgOrLifetime();
    if (!first) return nullptr;
    if ((unsigned)bb->size() < Mode2MinBBInsts) return nullptr;

    // splitting the entry block before an alloca relocates it into realbb and demotes it from static to dynamic, breaking AllocaInst::isStaticAlloca downstream; clamp `first` past the last entry alloca
    if (bb == &bb->getParent()->getEntryBlock())
    {
        Instruction* lastalloca = nullptr;
        for (Instruction& i : *bb)
        {
            if (isa<AllocaInst>(&i)) lastalloca = &i;
        }
        if (lastalloca)
        {
            Instruction* after = lastalloca->getNextNode();
            if (!after) return nullptr;
            BasicBlock::iterator seek(first);
            while (seek != bb->end() && &*seek != after) ++seek;
            if (seek != bb->end()) first = &*seek;
            else first = after;
        }
    }

    unsigned splittable = 0;
    for (auto it = BasicBlock::iterator(first); it != bb->end(); ++it)
    {
        if (&*it == bb->getTerminator()) break;
        ++splittable;
    }
    if (splittable == 0) return nullptr;

    const unsigned pick = (unsigned)(rng() % splittable);
    BasicBlock::iterator it(first);
    for (unsigned i = 0; i < pick; ++i) ++it;
    if (it == bb->end()) return nullptr;
    if (&*it == bb->getTerminator()) return nullptr;
    if (isa<PHINode>(&*it)) return nullptr;
    return &*it;
}

struct PolluteSlot
{
    AllocaInst* Base;
    int FieldIdx;
    Type* BaseTy;
    Type* RawTy;
    bool IsPtr;
    IntegerType* IntTy;
};

static Value* MaterializeSlotPtr(IRBuilder<>& b, const PolluteSlot& s)
{
    if (s.FieldIdx < 0) return s.Base;
    LLVMContext& c = b.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    return b.CreateInBoundsGEP(s.BaseTy, s.Base, { ConstantInt::get(i32, 0), ConstantInt::get(i32, s.FieldIdx) }, "HashopqPolluteGep");
}

static Value* EmitSlotLoad(IRBuilder<>& b, const PolluteSlot& s)
{
    Value* ptr = MaterializeSlotPtr(b, s);
    LoadInst* ld = b.CreateLoad(s.RawTy, ptr, "HashopqPolluteLoad");
    if (!s.IsPtr) return ld;
    return b.CreatePtrToInt(ld, s.IntTy, "HashopqPolluteLoadI");
}

static void EmitSlotStore(IRBuilder<>& b, const PolluteSlot& s, Value* intval, bool volatilestore)
{
    Value* ptr = MaterializeSlotPtr(b, s);
    Value* v = intval;
    if (s.IsPtr) v = b.CreateIntToPtr(intval, s.RawTy, "HashopqPolluteIntP");
    StoreInst* st = b.CreateStore(v, ptr);
    if (volatilestore) st->setVolatile(true);
}

static void CollectPolluteSlots(Function& f, IntegerType* i32, IntegerType* i64, SmallVectorImpl<PolluteSlot>& out32, SmallVectorImpl<PolluteSlot>& out64)
{
    for (Instruction& i : f.getEntryBlock())
    {
        auto* a = dyn_cast<AllocaInst>(&i);
        if (!a || !a->isStaticAlloca()) continue;
        Type* ty = a->getAllocatedType();

        if (ty->isIntegerTy(32)) { out32.push_back({ a, -1, ty, ty, false, i32 }); continue; }
        if (ty->isIntegerTy(64)) { out64.push_back({ a, -1, ty, ty, false, i64 }); continue; }
        if (ty->isPointerTy())
        {
            out64.push_back({ a, -1, ty, ty, true, i64 });
            continue;
        }
        if (auto* st = dyn_cast<StructType>(ty))
        {
            for (unsigned fi = 0; fi < st->getNumElements(); ++fi)
            {
                Type* ft = st->getElementType(fi);
                if (ft->isIntegerTy(32)) out32.push_back({ a, (int)fi, ty, ft, false, i32 });
                else if (ft->isIntegerTy(64)) out64.push_back({ a, (int)fi, ty, ft, false, i64 });
                else if (ft->isPointerTy()) out64.push_back({ a, (int)fi, ty, ft, true, i64 });
            }
        }
    }
}

struct HashConsts
{
    uint64_t K0;
    uint64_t K1;
    uint64_t K2;
    uint64_t K3;
    uint64_t Kmix;
};

static HashConsts RollHashConsts(std::mt19937_64& rng)
{
    HashConsts h;
    h.K0 = ((uint64_t)rng()) | 1ull;
    h.K1 = ((uint64_t)rng()) | 1ull;
    h.K2 = ((uint64_t)rng()) | 1ull;
    h.K3 = ((uint64_t)rng()) | 1ull;
    h.Kmix = (uint64_t)rng();
    return h;
}


static uint64_t ComputeHashCPU(uint64_t x, const HashConsts& hc)
{
    uint64_t r = x;
    r ^= r >> 30; r *= hc.K0;
    r ^= r >> 27; r *= hc.K1;
    r ^= r >> 31;
    r ^= hc.Kmix;
    r ^= r >> 29; r *= hc.K2;
    r ^= r >> 25; r *= hc.K3;
    r ^= r >> 32;
    return r;
}

static Value* EmitHashIR(IRBuilder<>& b, Value* xi64, IntegerType* i64, const HashConsts& hc)
{
    Value* r = InsertFoldBarrier(b, xi64);

    Value* s1 = b.CreateLShr(r, ConstantInt::get(i64, 30), "HashopqR1S1");
    r = b.CreateXor(r, s1, "HashopqR1X1");
    r = b.CreateMul(r, ConstantInt::get(i64, hc.K0), "HashopqR1M1");
    Value* s2 = b.CreateLShr(r, ConstantInt::get(i64, 27), "HashopqR1S2");
    r = b.CreateXor(r, s2, "HashopqR1X2");
    r = b.CreateMul(r, ConstantInt::get(i64, hc.K1), "HashopqR1M2");
    Value* s3 = b.CreateLShr(r, ConstantInt::get(i64, 31), "HashopqR1S3");
    r = b.CreateXor(r, s3, "HashopqR1X3");

    Value* kmix = InsertFoldBarrier(b, ConstantInt::get(i64, hc.Kmix));
    r = b.CreateXor(r, kmix, "HashopqMix");

    Value* s4 = b.CreateLShr(r, ConstantInt::get(i64, 29), "HashopqR2S1");
    r = b.CreateXor(r, s4, "HashopqR2X1");
    r = b.CreateMul(r, ConstantInt::get(i64, hc.K2), "HashopqR2M1");
    Value* s5 = b.CreateLShr(r, ConstantInt::get(i64, 25), "HashopqR2S2");
    r = b.CreateXor(r, s5, "HashopqR2X2");
    r = b.CreateMul(r, ConstantInt::get(i64, hc.K3), "HashopqR2M2");
    Value* s6 = b.CreateLShr(r, ConstantInt::get(i64, 32), "HashopqR2S3");
    r = b.CreateXor(r, s6, "HashopqFinal");

    return r;
}

static Value* WidenToI64(IRBuilder<>& b, Value* v, IntegerType* i64)
{
    if (v->getType() == i64) return v;
    if (v->getType()->isIntegerTy()) return b.CreateZExt(v, i64, "HashopqZx");
    return nullptr;
}

static Value* NormalizeToI64(IRBuilder<>& b, Value* v, IntegerType* i64)
{
    Type* ty = v->getType();
    if (ty == i64) return v;
    if (ty->isPointerTy()) return b.CreatePtrToInt(v, i64, "HashopqAuxP2I");
    if (ty->isIntegerTy())
    {
        unsigned w = cast<IntegerType>(ty)->getBitWidth();
        if (w < 64) return b.CreateZExt(v, i64, "HashopqAuxZx");
        if (w > 64) return b.CreateTrunc(v, i64, "HashopqAuxTr");
        return v;
    }
    return nullptr;
}

static std::vector<Value*> HarvestAuxValues(IRBuilder<>& b, DominatorTree& dt, IntegerType* i64, unsigned count, std::mt19937_64& rng)
{
    std::vector<Value*> out;
    BasicBlock* ipbb = b.GetInsertBlock();
    if (!ipbb) return out;
    Function* f = ipbb->getParent();

    Instruction* ip = nullptr;
    if (b.GetInsertPoint() != ipbb->end()) ip = &*b.GetInsertPoint();

    SmallVector<Value*, 32> candidates;

    for (Argument& a : f->args())
    {
        Type* ty = a.getType();
        if (ty->isIntegerTy() || ty->isPointerTy()) candidates.push_back(&a);
    }

    for (BasicBlock& bb : *f)
    {
        const bool samebb = (&bb == ipbb);
        if (!samebb && !dt.dominates(&bb, ipbb)) continue;
        for (Instruction& i : bb)
        {
            if (samebb && ip && (&i == ip || !i.comesBefore(ip))) break;
            Type* ty = i.getType();
            if (ty->isIntegerTy() || ty->isPointerTy()) candidates.push_back(&i);
        }
    }

    if (candidates.empty()) return out;

    const unsigned n = std::min<unsigned>(count, (unsigned)candidates.size());
    for (unsigned i = 0; i < n; ++i)
    {
        unsigned j = i + (unsigned)(rng() % ((unsigned)candidates.size() - i));
        std::swap(candidates[i], candidates[j]);
    }

    for (unsigned i = 0; i < n; ++i)
    {
        Value* v = NormalizeToI64(b, candidates[i], i64);
        if (v) out.push_back(v);
    }
    return out;
}

// operand dominance check uses switchSrc->getTerminator() as the probe point so the cloned instruction's none trivial operands all dominate the switch→decoy edge; dropping the dominance check would clone instructions whose operands aren't visible from the decoy and crash the verifier with a use before def
static bool CanCloneWithDominance(const Instruction& i, BasicBlock* switchsrc, DominatorTree& dt, const ValueToValueMapTy& vmap)
{
    for (const Use& u : i.operands())
    {
        Value* op = u.get();
        if (!op) continue;
        if (isa<Constant>(op)) continue;
        if (isa<Argument>(op)) continue;
        if (isa<BasicBlock>(op)) continue;
        if (isa<MetadataAsValue>(op)) continue;
        if (vmap.count(op)) continue;
        if (auto* oi = dyn_cast<Instruction>(op))
        {
            if (dt.dominates(oi, switchsrc->getTerminator())) continue;
            return false;
        }
        return false;
    }
    return true;
}

static unsigned DiamondCloneDonorInto(BasicBlock* donor, BasicBlock* decoy, BasicBlock* switchsrc, DominatorTree& dt, std::mt19937_64& rng, unsigned maxclone)
{
    if (maxclone == 0) return 0;
    if (!donor || !decoy) return 0;

    ValueToValueMapTy vmap;
    unsigned cloned = 0;
    const uint64_t mutnonce = rng();

    for (Instruction& i : *donor)
    {
        if (cloned >= maxclone) break;
        if (i.isTerminator()) break;

        if (isa<PHINode>(&i)) continue;
        if (isa<AllocaInst>(&i)) continue;
        if (isa<CallBase>(&i)) continue;
        if (isa<LandingPadInst>(&i)) continue;
        if (isa<CatchPadInst>(&i)) continue;
        if (isa<CleanupPadInst>(&i)) continue;
        if (i.isAtomic()) continue;
        if (isa<FenceInst>(&i)) continue;
        if (i.mayHaveSideEffects()) continue;

        if (!CanCloneWithDominance(i, switchsrc, dt, vmap)) continue;

        Instruction* clone = i.clone();
        clone->setName("");
        clone->insertInto(decoy, decoy->end());
        RemapInstruction(clone, vmap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);

        // strip inherited mbagen.escalate tags
        clone->setMetadata("mbagen.escalate", nullptr);

        if (auto* bo = dyn_cast<BinaryOperator>(clone))
        {
            if ((rng() & 1u) == 0)
            {
                Instruction::BinaryOps newop = bo->getOpcode();
                switch (bo->getOpcode())
                {
                    case Instruction::Add: newop = Instruction::Sub; break;
                    case Instruction::Sub: newop = Instruction::Add; break;
                    case Instruction::And: newop = Instruction::Or;  break;
                    case Instruction::Or:  newop = Instruction::And; break;
                    case Instruction::Xor: newop = Instruction::Or;  break;
                    case Instruction::Mul: newop = Instruction::Add; break;
                    default: break;
                }
                if (newop != bo->getOpcode())
                {
                    IRBuilder<> b(bo);
                    Value* nb = b.CreateBinOp(newop, bo->getOperand(0), bo->getOperand(1));
                    bo->replaceAllUsesWith(nb);
                    vmap[&i] = nb;
                    bo->eraseFromParent();
                    ++cloned;
                    continue;
                }
            }
            for (unsigned op = 0; op < bo->getNumOperands(); ++op)
            {
                if (auto* ci = dyn_cast<ConstantInt>(bo->getOperand(op)))
                {
                    if ((rng() % 100u) < 50u)
                    {
                        bo->setOperand(op, ConstantInt::get(ci->getType(), ci->getZExtValue() ^ mutnonce));
                    }
                }
            }
        }

        vmap[&i] = clone;
        ++cloned;
    }

    return cloned;
}

// empty BB terminator check MUST precede isEHPad because LLVM's BasicBlock::isEHPad dereferences getFirstNonPHI() which returns nullptr for empty BBs; reordering these two tests crashes on any empty BB a prior pass left in the function
static void CollectDonors(Function& f, BasicBlock* switchsrc, SmallVectorImpl<BasicBlock*>& out)
{
    for (BasicBlock& bb : f)
    {
        if (&bb == switchsrc) continue;
        if (!bb.getTerminator()) continue;
        if (bb.isEHPad()) continue;
        if (IsDecoyBlock(&bb)) continue;
        out.push_back(&bb);
    }
}

static void FillDecoyBlock(Function& f, BasicBlock* decoy, BasicBlock* switchsrc, BasicBlock* fallthrough_, ArrayRef<BasicBlock*> donors, DominatorTree& dt, std::mt19937_64& rng, const SmallVectorImpl<PolluteSlot>& slots32, const SmallVectorImpl<PolluteSlot>& slots64, unsigned donorclonecap)
{
    LLVMContext& c = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);

    unsigned diamondcloned = 0;
    if (!donors.empty())
    {
        BasicBlock* donor = donors[rng() % donors.size()];
        diamondcloned = DiamondCloneDonorInto(donor, decoy, switchsrc, dt, rng, donorclonecap);
    }

    IRBuilder<> fb(decoy);
    fb.SetInsertPoint(decoy);

    const bool have32 = !slots32.empty();
    const bool have64 = !slots64.empty();

    if (!have32 && !have64)
    {
        (void)EmitSinkLoad(fb, *f.getParent(), i64, "HashopqDecoySink");
        fb.CreateBr(fallthrough_);
        MarkDecoyBlock(decoy);
        return;
    }

    const unsigned opspan = DecoyMaxTailOps - DecoyMinTailOps + 1u;
    unsigned targetops = DecoyMinTailOps + (unsigned)(rng() % opspan);
    if (diamondcloned >= targetops) targetops = 1;
    else targetops -= diamondcloned;

    Value* acc = nullptr;
    IntegerType* accty = nullptr;

    auto pickslot = [&](IntegerType* ity) -> const PolluteSlot&
    {
        auto& slots = (ity == i64) ? slots64 : slots32;
        return slots[rng() % slots.size()];
    };

    for (unsigned n = 0; n < targetops; ++n)
    {
        IntegerType* ity;
        if (have32 && have64) ity = (rng() & 1) ? i64 : i32;
        else ity = have64 ? i64 : i32;

        if (acc && accty != ity) acc = nullptr;

        if (!acc)
        {
            acc = EmitSlotLoad(fb, pickslot(ity));
            accty = ity;
            continue;
        }

        Value* rhs = EmitSlotLoad(fb, pickslot(ity));
        switch (rng() % 6)
        {
            case 0: acc = fb.CreateXor(acc, rhs, "HashopqFillXor"); break;
            case 1: acc = fb.CreateAdd(acc, rhs, "HashopqFillAdd"); break;
            case 2: acc = fb.CreateSub(acc, rhs, "HashopqFillSub"); break;
            case 3: acc = fb.CreateAnd(acc, rhs, "HashopqFillAnd"); break;
            case 4: acc = fb.CreateOr(acc, rhs, "HashopqFillOr"); break;
            default: acc = fb.CreateMul(acc, rhs, "HashopqFillMul"); break;
        }

        if ((rng() % 100u) < DecoyStoreChancePct) EmitSlotStore(fb, pickslot(ity), acc, false);
    }

    if (acc) EmitSlotStore(fb, pickslot(accty), acc, true);

    fb.CreateBr(fallthrough_);
    MarkDecoyBlock(decoy);
}

// terminator check MUST precede isEHPad for the same empty-BB null-deref reason as CollectDonors; isEHPad on a BB with no terminator crashes on getFirstNonPHI() returning nullptr
static bool IsEHOrFuncletInterior(BasicBlock* bb)
{
    Instruction* term = bb->getTerminator();
    if (!term) return true;
    if (bb->isEHPad()) return true;
    if (isa<CatchReturnInst>(term) || isa<CleanupReturnInst>(term) || isa<ResumeInst>(term)) return true;
    for (Instruction& i : *bb)
    {
        if (auto* cb = dyn_cast<CallBase>(&i))
        {
            if (cb->countOperandBundlesOfType(LLVMContext::OB_funclet) > 0) return true;
        }
    }
    return false;
}

static unsigned StealIntoHead(BasicBlock* headbb, BasicBlock* realbb, unsigned maxsteal)
{
    unsigned stolen = 0;
    while (stolen < maxsteal)
    {
        Instruction* first = realbb->getFirstNonPHIOrDbgOrLifetime();
        if (!first || first->isTerminator()) break;

        if (isa<CallBase>(first)) break;
        if (isa<AllocaInst>(first)) break;
        if (isa<LandingPadInst>(first)) break;
        if (isa<CatchPadInst>(first)) break;
        if (isa<CleanupPadInst>(first)) break;
        if (first->isAtomic()) break;
        if (isa<FenceInst>(first)) break;
        if (first->mayHaveSideEffects()) break;

        bool opsok = true;
        for (Use& op : first->operands())
        {
            Value* v = op.get();
            if (auto* oi = dyn_cast<Instruction>(v))
            {
                if (oi->getParent() == realbb) { opsok = false; break; }
            }
        }
        if (!opsok) break;

        first->removeFromParent();
        first->insertInto(headbb, headbb->end());
        ++stolen;
    }
    return stolen;
}

static void ApplyBlanketSkipTag(LLVMContext& c, BasicBlock* headbb, Instruction* headpivot, ArrayRef<BasicBlock*> decoybbs)
{
    Metadata* skipops[1] = { MDString::get(c, "hashopq_skip") };
    MDNode* skipnode = MDNode::get(c, skipops);

    auto blanket = [&](BasicBlock* target, Instruction* afterthis)
    {
        BasicBlock::iterator it = afterthis ? std::next(BasicBlock::iterator(afterthis)) : target->begin();
        for (; it != target->end(); ++it)
        {
            MDNode* existing = it->getMetadata("mbagen.escalate");
            if (existing && existing->getNumOperands() > 0)
            {
                if (auto* ms = dyn_cast<MDString>(existing->getOperand(0).get()))
                {
                    if (ms->getString() == "poly_const") continue;
                }
            }
            it->setMetadata("mbagen.escalate", skipnode);
        }
    };

    blanket(headbb, headpivot);
    for (BasicBlock* d : decoybbs) blanket(d, nullptr);
}

// every decoy adds a new predecessor edge into fallthrough, and LLVM's verifier requires one PHI incoming entry per pred edge; reuse the existing incoming from preedgepred (same semantic edge) so a hypothetical ~2^-64 collision firing a decoy evaluates to a sensible value rather than undef
static void UpdateFallThroughPHIs(BasicBlock* fallthrough_, BasicBlock* preedgepred, ArrayRef<BasicBlock*> decoybbs)
{
    for (PHINode& phi : fallthrough_->phis())
    {
        const int srcidx = phi.getBasicBlockIndex(preedgepred);
        Value* srcval = (srcidx >= 0) ? phi.getIncomingValue((unsigned)srcidx) : UndefValue::get(phi.getType());
        for (BasicBlock* d : decoybbs) phi.addIncoming(srcval, d);
    }
}

struct Mode1Site
{
    BranchInst* Br;
    ICmpInst* Cmp;
    Value* V;
    uint64_t ConstBits;
    unsigned Bw;
    bool IsEq;
};

static bool MatchMode1Shape(BranchInst* br, Mode1Site& out)
{
    if (!br->isConditional()) return false;
    if (SiteAlreadyRewritten(br)) return false;

    if (IsEHOrFuncletInterior(br->getParent())) return false;

    auto* cmp = dyn_cast<ICmpInst>(br->getCondition());
    if (!cmp) return false;
    if (SiteAlreadyRewritten(cmp)) return false;
    if (!cmp->hasOneUse() || *cmp->user_begin() != br) return false;

    const auto p = cmp->getPredicate();
    if (p != CmpInst::ICMP_EQ && p != CmpInst::ICMP_NE) return false;

    Value* lhs = cmp->getOperand(0);
    Value* rhs = cmp->getOperand(1);
    auto* ci = dyn_cast<ConstantInt>(rhs);
    Value* v = lhs;
    if (!ci) { ci = dyn_cast<ConstantInt>(lhs); v = rhs; }
    if (!ci) return false;
    if (isa<Constant>(v)) return false;
    if (!v->getType()->isIntegerTy()) return false;

    const unsigned bw = v->getType()->getIntegerBitWidth();
    if (bw < 1 || bw > 64) return false;

    for (BasicBlock* s : br->successors())
    {
        if (s->isEHPad()) return false;
    }

    out.Br = br;
    out.Cmp = cmp;
    out.V = v;
    out.ConstBits = ci->getZExtValue();
    out.Bw = bw;
    out.IsEq = (p == CmpInst::ICMP_EQ);
    return true;
}

static bool TryRewriteIfCheckSite(Function& f, const Mode1Site& site, DominatorTree& dt)
{
    LLVMContext& c = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);

    BranchInst* br = site.Br;
    ICmpInst* cmp = site.Cmp;
    BasicBlock* headbb = br->getParent();

    BasicBlock* matchdest = site.IsEq ? br->getSuccessor(0) : br->getSuccessor(1);
    BasicBlock* nonmatchdest = site.IsEq ? br->getSuccessor(1) : br->getSuccessor(0);

    HashConsts hc = RollHashConsts(Rng);
    const uint64_t constmask = (site.Bw >= 64) ? ~uint64_t(0) : ((uint64_t(1) << site.Bw) - 1u);
    const uint64_t constzext = site.ConstBits & constmask;
    const uint64_t htrueraw = ComputeHashCPU(constzext, hc);

    SmallVector<BasicBlock*, 32> donors;
    CollectDonors(f, headbb, donors);

    SmallVector<PolluteSlot, 32> slots32, slots64;
    CollectPolluteSlots(f, i32, i64, slots32, slots64);

    // headpivot MUST live in headbb (not cmp's parent); under -O3 GVN/LICM may hoist the icmp into a dominating block, and cmp->getPrevNode() would then return an instruction from a different BB; ApplyBlanketSkipTag iterating from that instruction against headbb->end() is undefined behaviour and usually an access violation
    Instruction* headpivot = br->getPrevNode();

    IRBuilder<> b(br);

    Value* vi64 = WidenToI64(b, site.V, i64);
    if (!vi64) return false;

    Value* h = EmitHashIR(b, vi64, i64, hc);

    const uint64_t sitenonce = Rng();
    Value* noncev = InsertFoldBarrier(b, ConstantInt::get(i64, sitenonce));
    Value* hxored = b.CreateXor(h, noncev, "HashopqM1HXor");

    const uint64_t esck = Rng();
    Value* hfinal = b.CreateXor(hxored, ConstantInt::get(i64, esck), "HashopqM1HFinal");
    TagEscalateConstMBA(hfinal);

    const uint64_t truecase = (htrueraw ^ sitenonce) ^ esck;

    const unsigned fanspan = Mode1FanoutMax - Mode1FanoutMin + 1u;
    const unsigned fanout = Mode1FanoutMin + (unsigned)(Rng() % fanspan);

    // empty decoy BBs are created with no InsertBefore so they land at the function's end; prevents the edge case where nonmatchdest happens to be the function entry on a self loop, which would otherwise promote a freshly created decoy to the new entry and invalidate the module
    SmallVector<BasicBlock*, 32> decoybbs;
    decoybbs.reserve(fanout);
    for (unsigned i = 0; i < fanout; ++i)
    {
        BasicBlock* d = BasicBlock::Create(c, "Cont", &f);
        decoybbs.push_back(d);
    }

    // br MUST be erased BEFORE the switch is built at headbb's end; creating the switch at br's position before erasing would leave headbb with two terminators (switch mid block, br at end); invalid IR for the window between those two steps
    br->eraseFromParent();
    b.SetInsertPoint(headbb);

    SwitchInst* sw = b.CreateSwitch(hfinal, nonmatchdest, fanout + 1);
    sw->addCase(ConstantInt::get(i64, truecase), matchdest);

    std::unordered_set<uint64_t> used;
    used.insert(truecase);
    for (unsigned i = 0; i < fanout; ++i)
    {
        uint64_t caseval;
        do { caseval = (uint64_t)Rng(); } while (!used.insert(caseval).second);
        sw->addCase(ConstantInt::get(i64, caseval), decoybbs[i]);
    }

    for (BasicBlock* d : decoybbs) FillDecoyBlock(f, d, headbb, nonmatchdest, donors, dt, Rng, slots32, slots64, Mode1DonorCloneCap);

    UpdateFallThroughPHIs(nonmatchdest, headbb, decoybbs);

    ApplyBlanketSkipTag(c, headbb, headpivot, decoybbs);

    MarkSiteRewritten(sw);
    if (cmp->use_empty()) cmp->eraseFromParent();

    return true;
}

static bool RunMode1OnFunction(Function& f)
{
    std::vector<Mode1Site> candidates;
    for (BasicBlock& bb : f)
    {
        if (bb.isEHPad()) continue;
        if (IsDecoyBlock(&bb)) continue;
        auto* br = dyn_cast<BranchInst>(bb.getTerminator());
        if (!br) continue;
        Mode1Site s;
        if (MatchMode1Shape(br, s)) candidates.push_back(s);
    }

    if (candidates.size() > Mode1PerFunctionCap) candidates.resize(Mode1PerFunctionCap);

    bool mutated = false;
    for (const Mode1Site& s : candidates)
    {
        DominatorTree dt;
        dt.recalculate(f);
        if (TryRewriteIfCheckSite(f, s, dt)) mutated = true;
    }
    return mutated;
}

static Value* BuildMode2HashInput(IRBuilder<>& b, DominatorTree& dt, IntegerType* i64, std::mt19937_64& rng, Module& m)
{
    const unsigned auxspan = AuxCountMax - AuxCountMin + 1u;
    const unsigned auxcount = AuxCountMin + (unsigned)(rng() % auxspan);
    std::vector<Value*> aux = HarvestAuxValues(b, dt, i64, auxcount, rng);

    Value* raw;
    if (aux.empty())
    {
        raw = EmitSinkLoad(b, m, i64, "HashopqM2AuxSink");
    }
    else
    {
        raw = aux[0];
        for (size_t ai = 1; ai < aux.size(); ++ai) raw = b.CreateXor(raw, aux[ai], "HashopqM2XMix");
    }

    EnsureHashSalt(m);
    LoadInst* saltld = b.CreateLoad(i64, HashSaltGV, true, "HashopqM2Salt");
    saltld->setAlignment(Align(8));
    raw = b.CreateXor(raw, saltld, "HashopqM2Salted");
    return raw;
}

static bool TryEmitMode2AtBB(Function& f, BasicBlock* bb, DominatorTree& dt)
{
    if (BBAlreadyProcessedMode2(bb)) return false;
    if (IsDecoyBlock(bb)) return false;
    if (SkipEntryMode2 && bb == &f.getEntryBlock()) return false;
    if (IsEHOrFuncletInterior(bb)) return false;
    if (bb->size() < Mode2MinBBInsts) return false;

    Instruction* splitat = PickInsertionPointMode2(bb, Rng);
    if (!splitat) return false;

    BasicBlock* realbb = bb->splitBasicBlock(splitat, "Cont");

    Instruction* splitbr = bb->getTerminator();
    Instruction* lastexisting = splitbr->getPrevNode();
    splitbr->eraseFromParent();

    unsigned stealcap = 0;
    {
        const unsigned rbsize = (unsigned)realbb->size();
        if (rbsize > RealBBMinResidue)
        {
            const unsigned headroom = rbsize - RealBBMinResidue;
            const unsigned ceiling = std::min(StealCeiling, headroom);
            stealcap = 1u + (unsigned)(Rng() % ceiling);
            const unsigned floor = std::min(StealFloor, ceiling);
            if (stealcap < floor) stealcap = floor;
        }
    }
    if (stealcap > 0) (void)StealIntoHead(bb, realbb, stealcap);

    IRBuilder<> builder(bb);
    LLVMContext& c = f.getContext();
    IntegerType* i32 = Type::getInt32Ty(c);
    IntegerType* i64 = Type::getInt64Ty(c);

    Value* x = BuildMode2HashInput(builder, dt, i64, Rng, *f.getParent());
    HashConsts hc = RollHashConsts(Rng);
    Value* h = EmitHashIR(builder, x, i64, hc);

    const uint64_t sitenonce = Rng();
    Value* noncev = InsertFoldBarrier(builder, ConstantInt::get(i64, sitenonce));
    Value* hxored = builder.CreateXor(h, noncev, "HashopqM2HXor");

    const uint64_t esck = Rng();
    Value* hfinal = builder.CreateXor(hxored, ConstantInt::get(i64, esck), "HashopqM2HFinal");
    TagEscalateConstMBA(hfinal);

    // donor + slot collection MUST happen BEFORE the decoy BBs are allocated; CollectDonors walks the function's BB list and those fresh decoy BBs would otherwise be visible as donor candidates, letting a decoy clone shape from another decoy and recursing on nothing useful
    SmallVector<BasicBlock*, 32> donors;
    CollectDonors(f, bb, donors);
    SmallVector<PolluteSlot, 32> slots32, slots64;
    CollectPolluteSlots(f, i32, i64, slots32, slots64);

    const unsigned fanspan = Mode2FanoutMax - Mode2FanoutMin + 1u;
    const unsigned fanout = Mode2FanoutMin + (unsigned)(Rng() % fanspan);

    SmallVector<BasicBlock*, 32> decoybbs;
    decoybbs.reserve(fanout);
    for (unsigned i = 0; i < fanout; ++i)
    {
        BasicBlock* d = BasicBlock::Create(c, "Cont", &f);
        decoybbs.push_back(d);
    }

    SwitchInst* sw = builder.CreateSwitch(hfinal, realbb, fanout);
    std::unordered_set<uint64_t> used;
    for (unsigned i = 0; i < fanout; ++i)
    {
        uint64_t caseval;
        do { caseval = (uint64_t)Rng(); } while (!used.insert(caseval).second);
        sw->addCase(ConstantInt::get(i64, caseval), decoybbs[i]);
    }

    for (BasicBlock* d : decoybbs) FillDecoyBlock(f, d, bb, realbb, donors, dt, Rng, slots32, slots64, Mode2DonorCloneCap);

    UpdateFallThroughPHIs(realbb, bb, decoybbs);

    ApplyBlanketSkipTag(c, bb, lastexisting, decoybbs);
    MarkBBProcessedMode2(bb);
    return true;
}

static BasicBlock* RealBBFromSplitMode2(BasicBlock* bb)
{
    auto* sw = dyn_cast<SwitchInst>(bb->getTerminator());
    return sw ? sw->getDefaultDest() : nullptr;
}

static bool RunMode2OnFunction(Function& f)
{
    SmallVector<BasicBlock*, 64> worklist;
    SmallPtrSet<BasicBlock*, 32> seen;
    for (BasicBlock& bb : f)
    {
        worklist.push_back(&bb);
        seen.insert(&bb);
    }

    unsigned emitted = 0;
    bool mutated = false;
    while (!worklist.empty() && emitted < Mode2PerFunctionCap)
    {
        BasicBlock* bb = worklist.pop_back_val();
        if (IsDecoyBlock(bb)) continue;
        if (BBAlreadyProcessedMode2(bb)) continue;

        DominatorTree dt;
        dt.recalculate(f);
        LoopInfo li;
        li.analyze(dt);
        if (SkipLoopsMode2 && li.getLoopFor(bb) != nullptr) continue;

        if (!TryEmitMode2AtBB(f, bb, dt)) continue;
        ++emitted;
        mutated = true;

        if (BasicBlock* realbb = RealBBFromSplitMode2(bb))
        {
            if (seen.insert(realbb).second) worklist.push_back(realbb);
        }
    }
    return mutated;
}

// Mode 1 MUST run before Mode 2 so the candidate collection sees the function's original CFG; running Mode 2 first injects switch terminators across the function that MatchMode1Shape would then skip (branches only), erasing half the Mode 1 coverage silently
static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (HasNoObfuscateAnnotation(f) || HasNoHashOpaqueAnnotation(f)) return false;
    if (!HasObfuscateAnnotation(f)) return false;

    bool mutated = false;
    mutated |= RunMode1OnFunction(f);
    mutated |= RunMode2OnFunction(f);
    return mutated;
}

bool RunHashOpaque(Module& m)
{
    if (!HashOpaqueEnable) return false;

    std::random_device rd;
    uint64_t seed = (uint64_t)rd();
    seed ^= (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count();
    seed ^= ((uint64_t)rd()) << 32;
    seed ^= 0x484153484F50515FULL;
    Rng.seed(seed);

    
    HashSaltGV = nullptr;

    bool mutated = false;
    for (Function& f : m) mutated |= ProcessFunction(f);
    return mutated;
}

PreservedAnalyses HashOpaquePass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunHashOpaque(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}