#ifndef _TAINT_H
#define _TAINT_H

#include "Analyzer.h"
#include "Common.h"
#include <vector>

using namespace llvm;

class TaintPass : public IterativeModulePass {

	private:
		void ErrorReturnFuncAnalysis(Function *F);
		void IdentifyErrorReturnVariables(Function *TargetFunc, std::set<Value*> &ErrorReturnVars);
		void BuildLocalErrorCFG(Function *TargetFunc);
		bool InterproceduralErrorAnalysis(Function *F);

	public:
        TaintPass(GlobalContext *Ctx_)
			: IterativeModulePass(Ctx_, "Taint") { }
		
		virtual bool doInitialization(Module *M);
		virtual bool doFinalization(llvm::Module *);
		virtual bool doModulePass(llvm::Module *M);

};

#endif