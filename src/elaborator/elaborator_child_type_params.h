#pragma once

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct Expr;
struct ModuleDecl;
struct ModuleItem;

struct SavedTypedef {
  std::string_view name;
  bool existed = false;
  DataType prev;
};

struct TypeParamAssignments {
  const ModuleItem* item;
  std::vector<std::pair<std::string_view, Expr*>> config;
  bool config_reset_all = false;
  std::vector<std::string_view> config_reset;
};

template <typename Overrides>
TypeParamAssignments TypeParamSourcesFor(const ModuleItem* item,
                                         const Overrides& overrides,
                                         const std::string& inst_path) {
  TypeParamAssignments from{item, {}, false, {}};
  for (const auto& ov : overrides) {
    if (ov.inst_path != inst_path) continue;
    if (ov.reset_all) from.config_reset_all = true;
    for (const auto& assignment : ov.params) {
      if (assignment.second != nullptr) {
        from.config.push_back(assignment);
      } else {
        from.config_reset.push_back(assignment.first);
      }
    }
  }
  return from;
}

struct AppliedTypeParams {
  std::vector<SavedTypedef> saved;
  TypedefMap written;
};

AppliedTypeParams ApplyChildTypeParams(const TypeParamAssignments& from,
                                       const ModuleDecl* child_decl,
                                       TypedefMap& typedefs,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag);

bool AllTypeParamsHaveDefaults(const ModuleDecl* decl);

void RestoreChildTypeParams(TypedefMap& typedefs,
                            const std::vector<SavedTypedef>& saved);

}  // namespace delta
