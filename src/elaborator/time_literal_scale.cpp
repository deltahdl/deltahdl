#include "elaborator/time_literal_scale.h"

#include <unordered_map>

#include "common/types.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

// Puts on `scale` whichever of its unit and precision `decl` declares.
template <typename Decl>
void TakeDeclaredTimescale(TimeScale& scale, const Decl& decl) {
  if (decl.has_timeunit) {
    scale.unit = decl.time_unit;
    scale.magnitude = decl.time_unit_magnitude;
  }
  if (decl.has_timeprecision) {
    scale.precision = decl.time_prec;
    scale.prec_magnitude = decl.time_prec_magnitude;
  }
}

const ModuleDecl* EnclosingDeclIn(const ModuleDecl* scope,
                                  const ModuleDecl* decl) {
  for (const auto* item : scope->items) {
    if (item->kind != ModuleItemKind::kNestedModuleDecl) continue;
    if (item->nested_module_decl == decl) return scope;
    const ModuleDecl* found = EnclosingDeclIn(item->nested_module_decl, decl);
    if (found != nullptr) return found;
  }
  return nullptr;
}

// The module, interface or program declaration `decl` is nested in, or null
// for one written outside every other.
const ModuleDecl* EnclosingDecl(const ModuleDecl* decl,
                                const CompilationUnit& unit) {
  for (const auto* scopes :
       {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
    for (const ModuleDecl* scope : *scopes) {
      const ModuleDecl* found = EnclosingDeclIn(scope, decl);
      if (found != nullptr) return found;
    }
  }
  return nullptr;
}

}  // namespace

TimeScale CompilationUnitTimescale(const CompilationUnit& unit) {
  TimeScale scale;
  if (unit.has_cu_timeunit) {
    scale.unit = unit.cu_time_unit;
    scale.magnitude = unit.cu_time_unit_magnitude;
  }
  if (unit.has_cu_timeprecision) {
    scale.precision = unit.cu_time_prec;
    scale.prec_magnitude = unit.cu_time_prec_magnitude;
  }
  return scale;
}

TimeScale ModuleTimescale(const ModuleDecl* decl, const CompilationUnit& unit) {
  const ModuleDecl* enclosing = EnclosingDecl(decl, unit);
  TimeScale scale;
  if (enclosing != nullptr) {
    scale = ModuleTimescale(enclosing, unit);
  } else if (decl->has_directive_timescale) {
    scale = decl->directive_timescale;
  } else {
    scale = CompilationUnitTimescale(unit);
  }
  TakeDeclaredTimescale(scale, *decl);
  return scale;
}

TimeScale PackageTimescale(const PackageDecl& pkg,
                           const TimeScale& unit_scale) {
  TimeScale scale =
      pkg.has_directive_timescale ? pkg.directive_timescale : unit_scale;
  TakeDeclaredTimescale(scale, pkg);
  return scale;
}

void ScaleTimeLiterals(const CompilationUnit& unit) {
  const TimeScale kUnitScale = CompilationUnitTimescale(unit);
  // An element's scale is resolved once, however many literals it holds.
  std::unordered_map<const ModuleDecl*, TimeScale> module_scales;
  for (const TimeLiteralSite& site : unit.time_literals) {
    TimeScale scale = kUnitScale;
    if (site.module != nullptr) {
      auto [it, added] = module_scales.try_emplace(site.module);
      if (added) it->second = ModuleTimescale(site.module, unit);
      scale = it->second;
    } else if (site.package != nullptr) {
      scale = PackageTimescale(*site.package, kUnitScale);
    }
    site.literal->real_val = TimeLiteralValue(site.literal->text, scale);
  }
}

}  // namespace delta
