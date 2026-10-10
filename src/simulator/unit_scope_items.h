#pragma once

#include <cstddef>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "simulator/unit_scopes.h"

namespace delta {

class SimContext;
struct ClassDecl;

// A task or function a compilation unit declares outside every class, which
// the unit's scope holds by its name; §8.24's out-of-block method body, which
// names its class, is the class's.
inline bool IsFreeUnitSubroutine(const ModuleItem* item) {
  return (item->kind == ModuleItemKind::kFunctionDecl ||
          item->kind == ModuleItemKind::kTaskDecl) &&
         item->method_class.empty();
}

// §3.12.1 (printed page 56): calls `fn(unit, scope)` for each compilation unit
// of `design` and the scope name its declarations stand under, held in
// `arena`: the one unit's under "$unit", or unit k's under "$unit#k" where the
// design is of several units. Nothing for a design built with no parsed unit.
template <typename Fn>
void ForEachUnitScope(const RtlirDesign* design, Arena& arena, Fn fn) {
  if (design->compilation_units.empty()) {
    if (design->compilation_unit == nullptr) return;
    fn(*design->compilation_unit,
       std::string_view(*arena.Create<std::string>(UnitScopes::ScopeName(-1))));
    return;
  }
  for (size_t k = 0; k < design->compilation_units.size(); ++k) {
    fn(*design->compilation_units[k],
       std::string_view(*arena.Create<std::string>(
           UnitScopes::ScopeName(static_cast<int>(k)))));
  }
}

// §3.12.1: the scope name of the compilation unit declaring the class `cls`
// (unit_scope_items.cpp), empty for a package's or a module's class or with no
// design behind it.
std::string_view UnitScopeOfClass(const RtlirDesign* design,
                                  const ClassDecl* cls, Arena& arena);

// §3.12.1: in a design of several units, registers the subroutines of the
// unit `mod` was declared in for the instance under `prefix`, by their bare
// names under the prefix (unit_scope_items.cpp). Nothing for a design of one
// unit.
void RegisterOwnUnitSubroutines(const RtlirDesign* design,
                                const RtlirModule* mod, std::string_view prefix,
                                SimContext& ctx, Arena& arena);

}  // namespace delta
