#ifndef DELTA_ELABORATOR_COVERGROUP_RULES_H
#define DELTA_ELABORATOR_COVERGROUP_RULES_H

#include <functional>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/covergroup_context.h"
#include "elaborator/value_kind.h"

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct CovergroupDecl;
struct ModuleDecl;
struct ModuleItem;

void ValidateCovergroup(const CovergroupDecl& cg, const CovergroupContext& ctx,
                        DiagEngine& diag);

struct ModuleCovergroupTables {
  const ValueScope& values;
  const std::unordered_set<std::string_view>& const_names;
};

void ValidateModuleCovergroups(const ModuleDecl* decl,
                               const ModuleCovergroupTables& tables,
                               const CovergroupDeclared& declared,
                               DiagEngine& diag);

using CovergroupTypeVisible = std::function<bool(std::string_view)>;

void ValidateCovergroupTypeCalls(const ModuleDecl* decl,
                                 const CovergroupTypeVisible& visible,
                                 DiagEngine& diag);

void ValidateEmbeddedCovergroups(const ClassDecl* cls,
                                 const std::vector<ModuleItem*>& scope_items,
                                 const CompilationUnit* unit,
                                 const CovergroupDeclared& unit_declared,
                                 DiagEngine& diag);

}  // namespace delta

#endif
