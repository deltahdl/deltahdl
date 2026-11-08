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
