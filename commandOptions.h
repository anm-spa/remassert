#ifndef LLVM_CLANG_COMMANDOPTIONS_H
#define LLVM_CLANG_COMMANDOPTIONS_H

#include "clang/Tooling/CommonOptionsParser.h"

using namespace llvm;

static cl::OptionCategory RacerOptCat("Static Analysis Options");
static cl::extrahelp CommonHelp(clang::tooling::CommonOptionsParser::HelpMessage);
static cl::extrahelp MoreHelp("\nMore help text...");


static cl::opt<bool> RA("ra",cl::desc("Data race analysis"), cl::cat(RacerOptCat));



#endif
