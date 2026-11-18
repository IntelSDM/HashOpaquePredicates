# Hash Opaque Predicates
Built for LLVM 19.1 - Windows x64 <br> <br>

This pass does a similar thing to [ConditionStomping](https://github.com/IntelSDM/ConditionStompingObfuscation); but using cityhash. <br>
There are 2 variants being emitted here:<br>

* Hijacking Normal conditons, we hash all the natural conditions as seen in condition stomping,  then insert loads of impossible hashes for false conditions. These are entirely unprovable.
* Inserting always false hash comparison conditions with fake impossible values on runtime variables.

This requires runtime analysis to reverse engineer them all. Defeating symbolic execution, AI, lifting/optimising/SMT. <br>
This is the paper which a lot of my opaques are built off, it proves that the cityhash approach is best here: 
[Novel Opaque Predicate Techniques to Counter Dynamic Symbolic Execution](https://www.sciopen.com/local/article_pdf/10.32604/cmc.2025.062743.pdf)
<br>
<img width="1974" height="849" alt="image" src="https://github.com/user-attachments/assets/6c24c4af-db61-4f54-a77f-f98707232ed3" /> <br>
<img width="1956" height="920" alt="image" src="https://github.com/user-attachments/assets/3b3776fc-d560-4914-9a1d-6ae90d5b3306" /><br>
<img width="1963" height="926" alt="image" src="https://github.com/user-attachments/assets/b70e8937-a592-4826-8ca1-c82ee7b20859" /><br>
<img width="1971" height="938" alt="image" src="https://github.com/user-attachments/assets/8dd3ab48-6bdb-456e-9fa0-90c0fe97c845" /><br>

## Annotations
```c
__attribute__((annotate("obfus")))
``` 
* Marks your function for the pass

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
