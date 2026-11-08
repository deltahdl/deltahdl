#pragma once

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"

namespace delta {

class Parser;

struct HeaderPartLocs {
  SourceLoc import_loc = SourceLoc::None();
  SourceLoc params_loc = SourceLoc::None();
  SourceLoc ports_loc = SourceLoc::None();
};

void ReportUnwrittenHeaderParts(const ModuleDecl& decl,
                                const HeaderPartLocs& at, DiagEngine& diag);

struct ParserClassHeaderHelpers {
  static void ParseHeadKeywords(Parser& p, ClassDecl* decl);
  static void ParseBaseType(Parser& p, ClassDecl* decl, bool is_implements,
                            Subclause subclause);
};

}  // namespace delta
