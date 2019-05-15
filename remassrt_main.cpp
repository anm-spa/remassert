/****************************************************************/
/*          All rights reserved (it will be changed)            */
/*          masud.abunaser@mdh.se                               */
/****************************************************************/

#include <cstdio>
#include <string>
#include <sstream>
#include "clang/AST/AST.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetOptions.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Parse/ParseAST.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Driver/Options.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Sema/Sema.h"
#include "clang/Basic/LangOptions.h"
#include "commandOptions.h"

using namespace llvm;
using namespace clang;
using namespace std;
using namespace clang::driver;
using namespace clang::tooling;

Rewriter TheRewriter;

class  PrintStmtextended:public PrinterHelper
{
public:
    ASTContext *context;
    PrintStmtextended(ASTContext &c):context(&c){}
    bool handledStmt (Stmt *E, raw_ostream &OS)
    {
        E->dumpPretty(*context);
        return true;
    }
};

void SplitFilename (const string& str, string &path, string &filename)
{
    size_t found;
    found=str.find_last_of("/\\");
    path=str.substr(0,found);
    filename=str.substr(found+1);
}

class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
public:
    MyASTVisitor(CompilerInstance *CI, llvm::raw_fd_ostream &assF) : astContext(&(CI->getASTContext())) {
        first_FDecl=false;
        isInTU=false;
        assertFile=&assF;
        TheRewriter.setSourceMgr(astContext->getSourceManager(), astContext->getLangOpts());
    }
    
    bool isAssertLinux(Stmt *s,string &strExpr)
    {
        if(!isa<ConditionalOperator>(s)) return false;
        // the macro expansion of assert is a conditional expression
        ConditionalOperator *COp=static_cast<ConditionalOperator *>(s);
        Expr *Cond=COp->getCond()->IgnoreImplicit();
        Expr *TE=COp->getTrueExpr();
        Expr *FE=COp->getFalseExpr();
        if(!Cond && !TE && !FE) return false;
        
        CallExpr *CExpr=dyn_cast<CallExpr>(FE);
        if(!CExpr) return false;
        if(!(CExpr->getDirectCallee()->getNameInfo().getAsString()=="__assert_fail")) return false;
                
        Expr *argExp1=CExpr->getArg(0)->IgnoreImplicit();
        if(!argExp1) return false;
        clang::StringLiteral *strLt=dyn_cast<clang::StringLiteral>(argExp1);
        if(!strLt) return false;
        llvm::errs()<<"Assert Expr: "<<strLt->getString().str();
        strExpr=strLt->getString().str();
        unsigned lineNo=TheRewriter.getSourceMgr().getExpansionLineNumber(s->getBeginLoc());
        //s->getBeginLoc().printToString(TheRewriter.getSourceMgr())
        *assertFile<<"ASSERT("<<fname<<","<<lineNo<<","<<strExpr<<").\n";
        return true;
        //return false;
    }
    
    bool isAssertOsx(Stmt *s,string &strExpr)
    {
        if(!isa<ConditionalOperator>(s)) return false;
        // the macro expansion of assert is a conditional expression
        ConditionalOperator *COp=static_cast<ConditionalOperator *>(s);
        Expr *Cond=COp->getCond()->IgnoreImplicit();
        Expr *TE=COp->getTrueExpr();
        Expr *FE=COp->getFalseExpr();
        if(!Cond && !TE && !FE) return false;
        
        CallExpr *CExpr=dyn_cast<CallExpr>(Cond);
        if(!CExpr) return false;
        if(!(CExpr->getDirectCallee()->getNameInfo().getAsString()=="__builtin_expect")) return false;
        
        CallExpr *CExpr1=dyn_cast<CallExpr>(TE);
        if(!TE) return false;
        if(!(CExpr1->getDirectCallee()->getNameInfo().getAsString()=="__assert_rtn")) return false;
        
        Expr *argExp1=CExpr1->getArg(CExpr1->getNumArgs()-1)->IgnoreImplicit();
        if(!argExp1) return false;
        clang::StringLiteral *strLt=dyn_cast<clang::StringLiteral>(argExp1);
        if(!strLt) return false;
        llvm::errs()<<"Assert Expr: "<<strLt->getString().str();
        strExpr=strLt->getString().str();
        unsigned lineNo=TheRewriter.getSourceMgr().getExpansionLineNumber(s->getBeginLoc());
        //s->getBeginLoc().printToString(TheRewriter.getSourceMgr())
        *assertFile<<"ASSERT("<<fname<<","<<lineNo<<","<<strExpr<<").\n";
        return true;
        //return false;
    }
    
    bool VisitStmt(Stmt *s) {
        string str;
        if(isAssertOsx(s,str)|| isAssertLinux(s,str))
        {   const char *data="dyn_assert_var = 1";
            StringRef strRef=StringRef(data);
            llvm::errs()<<"\n Assert Found\n";
            SourceLocation startLoc = TheRewriter.getSourceMgr().getFileLoc(s->getBeginLoc());
            SourceLocation endLoc = s->getEndLoc();
            
            if( endLoc.isMacroID() ){
                endLoc=TheRewriter.getSourceMgr().getImmediateExpansionRange(endLoc).getEnd();
                endLoc.dump(TheRewriter.getSourceMgr());
            }
            SourceRange expandedLoc( startLoc, endLoc );
            TheRewriter.ReplaceText(expandedLoc, strRef);
        }
        
        return true;
    }
    
    bool VisitFunctionDecl(FunctionDecl *f) {
        // Only function definitions (with bodies), not declarations.
        SourceLocation sl=f->getSourceRange().getBegin();
        if(TheRewriter.getSourceMgr().isInMainFile (sl) && !first_FDecl)
        {
            first_FDecl=true;
            
            const char *data="unsigned dyn_assert_var = 0;\n";
            StringRef strRef=StringRef(data);
            TheRewriter.InsertTextBefore(sl,strRef);
        }
        if(TheRewriter.getSourceMgr().isInMainFile (sl))
        {
            isInTU=true;
            fname=f->getName().str();
        }
        return true;
    }
    
private:
    bool first_FDecl;
    bool isInTU;
    std::string fname;
    llvm::raw_fd_ostream *assertFile;
    ASTContext *astContext;
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
    MyASTConsumer(CompilerInstance *CI, llvm::raw_fd_ostream &assF) : Visitor(CI,assF) {}
    
    // Override the method that gets called for each parsed top-level
    // declaration.
    virtual bool HandleTopLevelDecl(DeclGroupRef DR) {
        for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b)
            // Traverse the declaration using our AST visitor.
            Visitor.TraverseDecl(*b);
        return true;
    }
    
private:
    MyASTVisitor Visitor;
};

class MyFrontendAction : public ASTFrontendAction {
    llvm::raw_fd_ostream *_assF;
public:
    MyFrontendAction(llvm::raw_fd_ostream &assF) {_assF=&assF;}
    
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) {
        //TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
        return llvm::make_unique<MyASTConsumer>(&CI,*_assF);
    }
};

class MyFrontendActionFactory : public clang::tooling::FrontendActionFactory {
    llvm::raw_fd_ostream *_assF;
public:
    MyFrontendActionFactory (llvm::raw_fd_ostream &assF)
    {_assF=&assF;}
    
    virtual clang::FrontendAction *create () {
        return new MyFrontendAction(*_assF);
    }
};

int main(int argc,  const char **argv) {
    
    if (argc != 2) {
        llvm::errs() << "Usage: remassert <filename>\n";
        return 1;
    }
    
    CommonOptionsParser op(argc, argv, RacerOptCat);
    ClangTool Tool(op.getCompilations(), op.getSourcePathList());
    
    FileManager &FileMgr = Tool.getFiles();
    const FileEntry *FileIn = FileMgr.getFile(argv[1]);
    string path, fname,fpname,assert_fname;
    SplitFilename(FileIn->getName().str().c_str(),path,fname);
    fpname=path+"/noassert_"+fname;
    assert_fname=path+"/assert.txt";
    std::error_code error_code;
    llvm::raw_fd_ostream outFile(fpname, error_code, llvm::sys::fs::F_None);
    llvm::raw_fd_ostream assertFile(assert_fname, error_code, llvm::sys::fs::F_None);
    
    MyFrontendActionFactory actionF(assertFile);
    Tool.run(&actionF);
    const RewriteBuffer *RewriteBuf = TheRewriter.getRewriteBufferFor(TheRewriter.getSourceMgr().                                                       getMainFileID());
    
    llvm::outs() << string(RewriteBuf->begin(), RewriteBuf->end());
    if(RewriteBuf)
        TheRewriter.getEditBuffer(TheRewriter.getSourceMgr().getMainFileID()).write(outFile);
    else
        llvm::errs()<<"\nNo Assert found, original retains!!!\n";
    outFile.close();
    assertFile.close();
    
    return 0;
    
}

