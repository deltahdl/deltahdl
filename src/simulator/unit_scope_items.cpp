#include "simulator/unit_scope_items.h"

#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "simulator/sim_context.h"
#include "simulator/unit_scopes.h"

namespace delta {

// §3.12.1 (printed page 56): the name a design of one unit's compilation-unit
// frames are pushed with and its items keyed under, "$unit.name"; no package
// can be named so, `$` starting no identifier.
constexpr std::string_view kOneUnitScope = "$unit";

// §3.12.1: kOneUnitScope for a class the compilation unit itself declares
// (RtlirDesign::cu_class_decls), and an empty view for a package's or a
// module's class, or with no design behind the class. In a design of several
// units, the scope name of the unit declaring the class ("$unit#k").
std::string_view UnitScopeOfClass(const RtlirDesign* design,
                                  const ClassDecl* cls, Arena& arena) {
  if (design == nullptr) return {};
  if (design->compilation_units.empty()) {
    for (const ClassDecl* unit_cls : design->cu_class_decls) {
      if (unit_cls == cls) return kOneUnitScope;
    }
    return {};
  }
  std::string_view found;
  ForEachUnitScope(design, arena,
                   [&](const CompilationUnit& unit, std::string_view scope) {
                     for (const ClassDecl* unit_cls : unit.classes) {
                       if (unit_cls == cls) found = scope;
                     }
                   });
  return found;
}

// The compilation unit's classes to lower: the first of each name, and in a
// design of several units every unit's own, two units' classes of one name
// being two classes (§3.12.1).
std::vector<const ClassDecl*> UnitClassesToLower(const RtlirDesign* design) {
  std::unordered_set<std::string_view> names;
  std::unordered_set<const ClassDecl*> chosen;
  std::vector<const ClassDecl*> classes;
  for (const auto* cls : design->cu_class_decls) {
    if (!names.insert(cls->name).second) continue;
    chosen.insert(cls);
    classes.push_back(cls);
  }
  for (const auto* unit : design->compilation_units) {
    for (const auto* cls : unit->classes) {
      if (chosen.insert(cls).second) classes.push_back(cls);
    }
  }
  return classes;
}

// §3.12.1: in a design of several units, the instance under `prefix` reaches
// its own unit's subroutines by their bare names: under the prefix, as its own
// subroutines are registered, and under the bare names themselves for the
// first top, whose names stand under no prefix. The module's own subroutines,
// registered after this, take a name it shares over.
void EnterInstanceUnit(const RtlirDesign* design, const RtlirModule* mod,
                       std::string_view prefix, SimContext& ctx, Arena& arena) {
  if (mod->unit_index < 0) return;
  ctx.Units().SetInstanceUnit(prefix, mod->unit_index);
  const CompilationUnit* unit =
      design->compilation_units[static_cast<size_t>(mod->unit_index)];
  for (auto* item : unit->cu_items) {
    if (!IsFreeUnitSubroutine(item)) continue;
    ctx.RegisterFunction(*arena.Create<std::string>(std::string(prefix) +
                                                    std::string(item->name)),
                         item);
  }
}

}  // namespace delta
