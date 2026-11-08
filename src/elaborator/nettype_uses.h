#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;

void ReportNettypeNotNet(std::string_view nettype, std::string_view use,
                         SourceLoc loc, DiagEngine& diag);

void CheckNettypeUses(const ModuleDecl* decl, const CompilationUnit& unit,
                      const std::unordered_set<std::string_view>& nettypes,
                      DiagEngine& diag);

bool WrittenAsDataDeclaration(const ModuleItem* item);

void CheckUnitNettypeUses(const CompilationUnit* unit,
                          const std::unordered_set<std::string_view>& scoped,
                          DiagEngine& diag);

}  // namespace delta
