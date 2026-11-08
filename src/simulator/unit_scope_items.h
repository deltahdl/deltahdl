#pragma once

#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "simulator/unit_scopes.h"

namespace delta {

class SimContext;
struct ClassDecl;

inline bool IsFreeUnitSubroutine(const ModuleItem* item) {
  return (item->kind == ModuleItemKind::kFunctionDecl ||
          item->kind == ModuleItemKind::kTaskDecl) &&
         item->method_class.empty();
}

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

std::string_view UnitScopeOfClass(const RtlirDesign* design,
                                  const ClassDecl* cls, Arena& arena);

std::vector<std::pair<std::string_view, std::string_view>>
ScopeSameNamedUnitClasses(const RtlirDesign* design, Arena& arena);

void RegisterUnitTimeScales(const RtlirDesign* design, SimContext& ctx,
                            Arena& arena);

void RegisterUnitLets(const RtlirDesign* design, SimContext& ctx, Arena& arena);

std::vector<const ClassDecl*> UnitClassesToLower(const RtlirDesign* design);

void EnterInstanceUnit(const RtlirDesign* design, const RtlirModule* mod,
                       std::string_view prefix, SimContext& ctx, Arena& arena);

bool EnclosingDeclHoldsVariable(std::string_view prefix, std::string_view name,
                                const SimContext& ctx);

}  // namespace delta
