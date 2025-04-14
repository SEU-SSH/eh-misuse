// TO BE DONE

#include <llvm/Pass.h>
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Debug.h"
#include <llvm/IR/Module.h>
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h" 
#include "llvm/IR/BasicBlock.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include <map> 
#include <set>
#include <algorithm>
#include <vector> 
#include <utility>
#include <iostream>
#include <fstream>
#include <bits/stdc++.h>
#include "llvm/IR/CFG.h" 
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"
#include "Taint.h"
#include "Common.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/CallGraph.h"  
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Operator.h"

using namespace llvm;

void TaintPass::ErrorReturnFuncAnalysis(Function *F) {
    // Step 1: Identify all error code variables as taint sources
    std::set<Value*> ErrorCodeVars;
    bool isErrorReturnFunc = false;
    
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
                Value *Val = SI->getValueOperand();
                Value *Ptr = SI->getPointerOperand();
                
                // Check if a null pointer is stored
                if (isa<ConstantPointerNull>(Val)) {
                    errs() << "null pointer store: ";
                    printConsistentDebugLoc(SI);
                    ErrorCodeVars.insert(Ptr);
                }
                
                // Check if a negative constant is stored
                if (ConstantInt *CI = dyn_cast<ConstantInt>(Val)) {
                    if (CI->isNegative()) {
                        errs() << "negative constant: ";
                        printConsistentDebugLoc(SI);
                        ErrorCodeVars.insert(Ptr);
                    }
                }
            }

            if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                Function *Callee = CI->getCalledFunction();
                if (Callee && Callee->getName().find("ERR_PTR") != std::string::npos) {
                    errs() << "ERR_PTR: ";
                    printConsistentDebugLoc(CI);
                    ErrorCodeVars.insert(CI);
                }

                if (Callee && Callee->getName().find("PTR_ERR") != std::string::npos) {
                    errs() << "PTR_ERR: ";
                    printConsistentDebugLoc(CI);
                    ErrorCodeVars.insert(CI);
                }
            }
        }
    }
    
    // If no error codes are found, return directly
    if (ErrorCodeVars.empty()) {
        return;
    }
    
    errs() << "Found " << ErrorCodeVars.size() << " error code variables in function " 
           << F->getName() << ", running taint analysis...\n";
    
    // Step 2: Identify all possible sink points (function parameter pointers and return statements)
    std::set<Value*> SinkArgs;
    std::set<ReturnInst*> SinkReturns;
    
    // Identify function parameter pointers as sinks
    for (Argument &Arg : F->args()) {
        if (Arg.getType()->isPointerTy()) {
            SinkArgs.insert(&Arg);
            errs() << "Identified sink argument: " << Arg.getName() << "\n";
        }
    }
    
    // Identify all return statements as sinks
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
                SinkReturns.insert(RI);
            }
        }
    }
    
    // Step 3: Perform taint analysis
    std::set<Value*> TaintedValues; // Store all tainted values
    std::set<Value*> TaintedSinks;  // Store tainted sink points
    
    // Initialize work queue with all taint sources
    std::queue<Value*> WorkList;
    for (Value *ErrorCode : ErrorCodeVars) {
        TaintedValues.insert(ErrorCode);
        WorkList.push(ErrorCode);
    }
    
    // Execute taint propagation
    while (!WorkList.empty()) {
        Value *TaintedValue = WorkList.front();
        WorkList.pop();
        
        // Iterate through all instructions using this value
        for (User *U : TaintedValue->users()) {
            if (Instruction *I = dyn_cast<Instruction>(U)) {
                // Skip if instruction is not in the current function
                if (I->getFunction() != F) continue;
                
                // Skip if instruction is already tainted
                if (TaintedValues.count(I)) continue;
                
                bool NewTaint = false;
                
                // Taint propagation logic for different instruction types
                if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
                    // Load instruction: if pointer is tainted, result is tainted
                    if (LI->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
                    // Store instruction: if value is tainted, pointer is tainted
                    if (SI->getValueOperand() == TaintedValue) {
                        Value *Ptr = SI->getPointerOperand();
                        if (!TaintedValues.count(Ptr)) {
                            TaintedValues.insert(Ptr);
                            WorkList.push(Ptr);
                            
                            // Check if any parameter sink is tainted
                            for (Value *SinkArg : SinkArgs) {
                                if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Ptr)) {
                                    if (GEP->getPointerOperand() == SinkArg) {
                                        TaintedSinks.insert(SinkArg);
                                    }
                                } else if (Ptr == SinkArg) {
                                    TaintedSinks.insert(SinkArg);
                                }
                            }
                        }
                    }
                } else if (CastInst *CI = dyn_cast<CastInst>(I)) {
                    // Type cast instructions always propagate taint
                    NewTaint = true;
                } else if (PHINode *PHI = dyn_cast<PHINode>(I)) {
                    // PHI node: if any input is tainted, result is tainted
                    for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
                        if (PHI->getIncomingValue(i) == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I)) {
                    // GEP instruction: if base pointer is tainted, result is tainted
                    if (GEP->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (CallInst *CallI = dyn_cast<CallInst>(I)) {
                    // For function calls, check parameters and return values
                    for (unsigned i = 0; i < CallI->arg_size(); i++) {
                        if (CallI->getArgOperand(i) == TaintedValue) {
                            // If call has return value, it becomes tainted
                            if (!CallI->getType()->isVoidTy()) {
                                NewTaint = true;
                            }
                            break;
                        }
                    }
                } else if (BinaryOperator *BinOp = dyn_cast<BinaryOperator>(I)) {
                    // Binary operations: if any operand is tainted, result is tainted
                    if (BinOp->getOperand(0) == TaintedValue || 
                        BinOp->getOperand(1) == TaintedValue) {
                        NewTaint = true;
                    }
                } else {
                    // Other instructions: if any operand is tainted, result is tainted
                    for (Use &U : I->operands()) {
                        if (U.get() == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                }
                
                // If instruction is newly tainted, add to work queue
                if (NewTaint) {
                    TaintedValues.insert(I);
                    WorkList.push(I);
                }
            }
        }
    }
    
    // Step 4: Check if return statement sinks are tainted
    for (ReturnInst *RI : SinkReturns) {
        if (Value *RetVal = RI->getReturnValue()) {
            if (TaintedValues.count(RetVal)) {
                TaintedSinks.insert(RI);
                isErrorReturnFunc = true;
            }
        }
    }
    
    // Step 5: Output analysis results
    errs() << "\n--- Taint Analysis Results for function: " << F->getName() << " ---\n";
    errs() << "Total tainted values: " << TaintedValues.size() << "\n";
    errs() << "Tainted sink points: " << TaintedSinks.size() << "\n";
    
    if (!TaintedSinks.empty()) {
        errs() << "\nDetailed tainted sink points:\n";
        
        // Output tainted parameter pointers
        for (Value *Arg : SinkArgs) {
            if (TaintedSinks.count(Arg)) {
                errs() << "  PARAMETER: " << Arg->getName() << " [Tainted parameter pointer]\n";
            }
        }
        
        // Output tainted return statements
        for (ReturnInst *RI : SinkReturns) {
            if (TaintedSinks.count(RI)) {
                errs() << "  RETURN: ";
                printConsistentDebugLoc(RI);
                errs() << " ";
                RI->print(errs());
                errs() << " [Tainted return value]\n";
            }
        }
    }
    
    if (isErrorReturnFunc) {
        errs() << "\nFunction " << F->getName() << " identified as an error-propagating function\n";
        Ctx->ErrorReturnFuncs.insert(F);
        auto &CIS = Ctx->Callers[F];
        for (auto CI : CIS) {
            Function *TF = CI->getFunction();
            if (TF) {
                /*construct CCFG*/
            }
        }
    }
    
    errs() << "--- End of Taint Analysis ---\n\n";
}


void IdentifyMemoryPointers(Function *TargetFunc, std::set<Value*> &MemoryPointers) {
    std::set<Function*> MemAllocFuncs;
    
    // 预先识别内存分配函数
    Module *M = TargetFunc->getParent();
    for (auto &F : *M) {
        StringRef FName = F.getName();
        if (FName.contains("malloc") || FName.contains("alloc") || 
            FName.contains("kmalloc") || FName.contains("kvmalloc") ||
            FName.contains("kzalloc") || FName.contains("vmalloc")) {
            MemAllocFuncs.insert(&F);
        }
    }
    
    // 构建函数间CFG和指针传播追踪
    std::queue<Function*> WorkList;
    std::set<Function*> Visited;
    
    WorkList.push(TargetFunc);
    Visited.insert(TargetFunc);
    
    while (!WorkList.empty()) {
        Function *CurFunc = WorkList.front();
        WorkList.pop();
        
        for (auto &BB : *CurFunc) {
            for (auto &I : BB) {
                if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                    Function *Callee = CI->getCalledFunction();
                    
                    // 检查是否调用了内存分配函数
                    if (Callee && MemAllocFuncs.find(Callee) != MemAllocFuncs.end()) {
                        // 内存分配函数的返回值是指针
                        MemoryPointers.insert(CI);
                        errs() << "Found memory allocation: ";
                        CI->print(errs());
                        errs() << "\n";
                        
                        // 追踪指针流向
                        for (User *U : CI->users()) {
                            if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
                                if (SI->getValueOperand() == CI) {
                                    Value *Ptr = SI->getPointerOperand();
                                    MemoryPointers.insert(Ptr);
                                }
                            }
                        }
                    }
                    
                    // 将被调用函数加入工作列表，构建函数间CFG
                    if (Callee && Visited.find(Callee) == Visited.end()) {
                        WorkList.push(Callee);
                        Visited.insert(Callee);
                    }
                }
                
                // 追踪加载指令，可能是从已知内存指针加载值
                if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
                    Value *LoadPtr = LI->getPointerOperand();
                    if (MemoryPointers.find(LoadPtr) != MemoryPointers.end()) {
                        // 加载自内存指针的值，也是指针
                        MemoryPointers.insert(LI);
                    }
                }
            }
        }
    }
}


bool TaintPass::InterproceduralErrorAnalysis(Function *F) {
    // Identify all calls to known error-returning functions within this function
    std::set<CallInst*> ErrorReturnCalls;
    std::map<CallInst*, Value*> ErrorReturnVars;
    
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                Function *Callee = CI->getCalledFunction();
                
                // Direct call to known error-returning function
                if (Callee && Ctx->ErrorReturnFuncs.count(Callee)) {
                    ErrorReturnCalls.insert(CI);
                    ErrorReturnVars[CI] = CI;
                    continue;
                }
                
                // Indirect call through function pointer - check all possible callees
                if (!Callee) {
                    auto Callees = Ctx->Callees.find(CI);
                    if (Callees != Ctx->Callees.end()) {
                        for (Function *PotentialCallee : Callees->second) {
                            if (Ctx->ErrorReturnFuncs.count(PotentialCallee)) {
                                ErrorReturnCalls.insert(CI);
                                ErrorReturnVars[CI] = CI;
                                break;
                            }
                        }
                    }
                }
            }
        }
    }
    
    // If no calls to error-returning functions, return directly
    if (ErrorReturnCalls.empty()) {
        return false;
    }
    
    errs() << "Found " << ErrorReturnCalls.size() << " calls to error-returning functions in " 
           << F->getName() << ", running interprocedural taint analysis...\n";
    
    // Identify all return statements as sinks
    std::set<ReturnInst*> SinkReturns;
    for (auto &BB : *F) {
        for (auto &I : BB) {
            if (ReturnInst *RI = dyn_cast<ReturnInst>(&I)) {
                SinkReturns.insert(RI);
            }
        }
    }
    
    // Perform taint analysis
    std::set<Value*> TaintedValues; // Store all tainted values
    std::set<ReturnInst*> TaintedReturns;  // Store tainted return instructions
    
    // Initialize work queue with all taint sources
    std::queue<Value*> WorkList;
    for (auto &Entry : ErrorReturnVars) {
        Value *ErrorRetVal = Entry.second;
        TaintedValues.insert(ErrorRetVal);
        WorkList.push(ErrorRetVal);
    }
    
    // Execute taint propagation
    while (!WorkList.empty()) {
        Value *TaintedValue = WorkList.front();
        WorkList.pop();
        
        // Iterate through all instructions using this value
        for (User *U : TaintedValue->users()) {
            if (Instruction *I = dyn_cast<Instruction>(U)) {
                // Skip if instruction is not in the current function
                if (I->getFunction() != F) continue;
                
                // Skip if instruction is already tainted
                if (TaintedValues.count(I)) continue;
                
                bool NewTaint = false;
                
                // Taint propagation logic for different instruction types
                if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
                    // Load instruction: if pointer is tainted, result is tainted
                    if (LI->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
                    // Store instruction: if value is tainted, pointer is tainted
                    if (SI->getValueOperand() == TaintedValue) {
                        Value *Ptr = SI->getPointerOperand();
                        if (!TaintedValues.count(Ptr)) {
                            TaintedValues.insert(Ptr);
                            WorkList.push(Ptr);
                        }
                    }
                } else if (CastInst *CI = dyn_cast<CastInst>(I)) {
                    // Type cast instructions always propagate taint
                    NewTaint = true;
                } else if (PHINode *PHI = dyn_cast<PHINode>(I)) {
                    // PHI node: if any input is tainted, result is tainted
                    for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
                        if (PHI->getIncomingValue(i) == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I)) {
                    // GEP instruction: if base pointer is tainted, result is tainted
                    if (GEP->getPointerOperand() == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (CallInst *CallI = dyn_cast<CallInst>(I)) {
                    // For function calls, check parameters and return values
                    for (unsigned i = 0; i < CallI->arg_size(); i++) {
                        if (CallI->getArgOperand(i) == TaintedValue) {
                            // If call has return value, it becomes tainted
                            if (!CallI->getType()->isVoidTy()) {
                                NewTaint = true;
                            }
                            break;
                        }
                    }
                } else if (BinaryOperator *BinOp = dyn_cast<BinaryOperator>(I)) {
                    // Binary operations: if any operand is tainted, result is tainted
                    if (BinOp->getOperand(0) == TaintedValue || 
                        BinOp->getOperand(1) == TaintedValue) {
                        NewTaint = true;
                    }
                } else if (ReturnInst *RI = dyn_cast<ReturnInst>(I)) {
                    // Return instruction: if return value is tainted, mark it
                    Value *RetVal = RI->getReturnValue();
                    if (RetVal == TaintedValue) {
                        TaintedReturns.insert(RI);
                    }
                } else {
                    // Other instructions: if any operand is tainted, result is tainted
                    for (Use &Op : I->operands()) {
                        if (Op.get() == TaintedValue) {
                            NewTaint = true;
                            break;
                        }
                    }
                }
                
                // If instruction is newly tainted, add to work queue
                if (NewTaint) {
                    TaintedValues.insert(I);
                    WorkList.push(I);
                    
                    // Check if this is a return instruction with tainted value
                    if (ReturnInst *RI = dyn_cast<ReturnInst>(I)) {
                        Value *RetVal = RI->getReturnValue();
                        if (RetVal && TaintedValues.count(RetVal)) {
                            TaintedReturns.insert(RI);
                        }
                    }
                }
            }
        }
    }
    
    // Check if any return statement is tainted
    bool IsErrorPropagatingFunc = !TaintedReturns.empty();
    
    if (IsErrorPropagatingFunc) {
        errs() << "\nFunction " << F->getName() << " identified as an interprocedural error-propagating function\n";
        
        // Log the error propagation paths
        errs() << "Detailed taint propagation paths:\n";
        for (CallInst *CI : ErrorReturnCalls) {
            Function *Callee = CI->getCalledFunction();
            if (Callee) {
                errs() << "  Error source: call to " << Callee->getName() << " at ";
                printConsistentDebugLoc(CI);
                errs() << "\n";
            } else {
                // Handle indirect calls
                errs() << "  Error source: indirect function call at ";
                printConsistentDebugLoc(CI);
                errs() << "\n";
            }
        }
        
        for (ReturnInst *RI : TaintedReturns) {
            errs() << "  Error sink: return statement at ";
            printConsistentDebugLoc(RI);
            errs() << "\n";
        }
        
        // Add this function to the set of error-returning functions
        Ctx->ErrorReturnFuncs.insert(F);
        
        return true;
    }
    
    return false;
}

void TaintPass::BuildLocalErrorCFG(Function *TargetFunc) {
    errs() << "Building local CFG for error propagation in " << TargetFunc->getName() << ":\n";
    
    for (auto &BB : *TargetFunc) {
        for (auto &I : BB) {
            if (CallInst *CI = dyn_cast<CallInst>(&I)) {
                Function *SourceFunc = CI->getCalledFunction();
        
                // Handle direct calls
                if (SourceFunc && Ctx->ErrorReturnFuncs.count(SourceFunc)) {
                    errs() << "  Adding edge: " << SourceFunc->getName() << " -> " << TargetFunc->getName() << "\n";
                    
                    // Add the edge to the CFG
                    Ctx->addErrorPropagationEdge(SourceFunc, TargetFunc, CI);
                } 
                // Handle indirect calls
                else if (!SourceFunc) {
                    auto Callees = Ctx->Callees.find(CI);
                    if (Callees != Ctx->Callees.end()) {
                        for (Function *PotentialCallee : Callees->second) {
                            if (Ctx->ErrorReturnFuncs.count(PotentialCallee)) {
                                errs() << "  Adding edge (indirect): " << PotentialCallee->getName() 
                                      << " -> " << TargetFunc->getName() << "\n";
                                
                                // Add the edge to the CFG
                                Ctx->addErrorPropagationEdge(PotentialCallee, TargetFunc, CI);
                            }
                        }
                    }
                }
            }
        }
    }
}

bool TaintPass::doInitialization(Module *M) {
    
    // 
    for (auto &F : *M) {
        ErrorReturnFuncAnalysis(&F);
    }

    bool Changed = true;
    while (Changed) {
        Changed = false;
        for (auto &F : *M) {
            // Skip functions we've already identified
            if (Ctx->ErrorReturnFuncs.count(&F)) {
                continue;
            }
            
            // Check if this function propagates errors from other error-returning functions
            if (InterproceduralErrorAnalysis(&F)) {
                Changed = true;
            }
        }
    }

    for (auto &F :*M) {
        // Build local CFG for error propagation
        BuildLocalErrorCFG(&F);
    }

    return false;
}

bool TaintPass::doFinalization(Module *M) {
    return false;
}

bool TaintPass::doModulePass(Module *M) {

    

    return false;
}