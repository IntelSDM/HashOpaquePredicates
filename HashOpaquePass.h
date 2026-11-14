#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct HashOpaquePass : llvm::PassInfoMixin<HashOpaquePass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunHashOpaque(llvm::Module& m);

extern llvm::cl::opt<bool> HashOpaqueEnable;