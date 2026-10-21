#pragma once

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"

namespace delta {

class Parser;

// Where the parts of a design element's header that A.1.2 can leave out were
// written, each invalid where it was not.
struct HeaderPartLocs {
  SourceLoc import_loc = SourceLoc::None();
  SourceLoc params_loc = SourceLoc::None();
  SourceLoc ports_loc = SourceLoc::None();
};

// A.1.2: a checker's header is its name and an optional port list alone, the
// ( .* ) header of a module, an interface or a program writes nothing between
// the name and ( .* ), and an extern declaration's header has no ( .* ) form,
// since that form takes its ports from the extern declaration (§23.5). Reports
// each part of `decl`'s header, written `at`, that its form does not write.
void ReportUnwrittenHeaderParts(const ModuleDecl& decl,
                                const HeaderPartLocs& at, DiagEngine& diag);

// The parts of a class header, as A.1.2 writes class_declaration and
// interface_class_declaration.
struct ParserClassHeaderHelpers {
  // `virtual`, `interface`, `class`, the final specifier and a stray lifetime,
  // up to the class's name, reporting what the declaration's kind does not
  // write.
  static void ParseHeadKeywords(Parser& p, ClassDecl* decl);
  // One class type of an extends or an implements clause, with the arguments
  // written after it.
  static void ParseBaseType(Parser& p, ClassDecl* decl, bool is_implements,
                            Subclause subclause);
};

}  // namespace delta
