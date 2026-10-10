#pragma once

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"
#include "parser/scope_type_names.h"

using namespace delta;

// Parses each of `srcs` as a compilation unit of its own, the use model
// §3.12.1 (printed page 56) has a tool provide where each file is one. A
// package is visible in every unit, so each parse is handed the package names
// the units before it declared, which is what lets a later unit's
// `import p::*;` read p's type names as types.
inline std::vector<CompilationUnit*> ParseUnitsApart(
    const std::vector<std::string>& srcs, SourceManager& mgr, Arena& arena,
    DiagEngine& diag) {
  std::vector<CompilationUnit*> units;
  CompilationUnitScopeNames packages;
  for (const auto& src : srcs) {
    auto fid = mgr.AddFile("<unit>", src);
    Lexer lexer(mgr.FileContent(fid), fid, diag);
    Parser parser(lexer, arena, diag);
    parser.AdoptCompilationUnitScope(packages);
    units.push_back(parser.Parse());
    auto scope = parser.CompilationUnitScope();
    packages.packages.insert(scope.packages.begin(), scope.packages.end());
  }
  return units;
}
