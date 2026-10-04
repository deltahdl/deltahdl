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

// A saved typedef-map entry, so a type-parameter substitution made for one
// child elaboration can be undone afterwards (the map is shared across
// modules).
struct SavedTypedef {
  std::string_view name;
  bool existed = false;
  DataType prev;
};

// Where a type parameter's value assignment can come from: the instantiation,
// and the parameter overrides a configuration made for the instance (§33.4.3),
// which take precedence over it; `config_reset_all` is the configuration's
// empty `#()`, which returns every parameter to its default and so sets the
// instantiation's assignments aside.
struct TypeParamAssignments {
  const ModuleItem* item;
  std::vector<std::pair<std::string_view, Expr*>> config;
  bool config_reset_all = false;
};

// Gathers where the type parameters of the instance at `inst_path`, written as
// `item`, take their assignments from: the instantiation, and the parameter
// overrides a configuration recorded for that path in `overrides`, each an
// element carrying `inst_path`, `reset_all` and `params` (§33.4.3).
template <typename Overrides>
TypeParamAssignments TypeParamSourcesFor(const ModuleItem* item,
                                         const Overrides& overrides,
                                         const std::string& inst_path) {
  TypeParamAssignments from{item, {}, false};
  for (const auto& ov : overrides) {
    if (ov.inst_path != inst_path) continue;
    if (ov.reset_all) from.config_reset_all = true;
    for (const auto& assignment : ov.params) {
      if (assignment.second != nullptr) from.config.push_back(assignment);
    }
  }
  return from;
}

// §6.20.3/§23.10: resolve each of the child's type parameters to a concrete
// type and publish it in `typedefs` so the child's dependent declarations
// elaborate against the chosen type. A type parameter whose type could not be
// settled publishes nothing, so the child's declarations that depend on it are
// left unresolved rather than bound to a type the instantiation did not ask
// for. Returns the prior entries so the caller can restore the shared map after
// the child is elaborated.
std::vector<SavedTypedef> ApplyChildTypeParams(const TypeParamAssignments& from,
                                               const ModuleDecl* child_decl,
                                               TypedefMap& typedefs,
                                               const CompilationUnit* unit,
                                               DiagEngine& diag);

// Whether every type parameter `decl` declares has a default type (§6.20.3).
bool AllTypeParamsHaveDefaults(const ModuleDecl* decl);

// Puts back the typedef-map entries ApplyChildTypeParams replaced.
void RestoreChildTypeParams(TypedefMap& typedefs,
                            const std::vector<SavedTypedef>& saved);

}  // namespace delta
