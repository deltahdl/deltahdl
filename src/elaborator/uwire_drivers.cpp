#include "elaborator/uwire_drivers.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/unit_scope_order.h"
#include "parser/ast_expr.h"
#include "parser/ast_gate_type.h"
#include "parser/ast_module.h"

namespace delta {

// Whether two drivers reach a common bit: down every step both take, they name
// the same member or index ranges that meet, and where one stops short it
// reaches every bit beneath. A member beside an index names the bits of one
// structure two ways, which this does not line up, so they are not counted as
// meeting.
static bool PathsMeet(const UwirePath& a, const UwirePath& b) {
  const size_t kSteps = std::min(a.size(), b.size());
  for (size_t i = 0; i < kSteps; ++i) {
    if (a[i].member != b[i].member) return false;
    if (a[i].hi < b[i].lo || b[i].hi < a[i].lo) return false;
  }
  return true;
}

void UwireDrivers::Record(std::string_view name, std::string_view declared,
                          const UwirePath& path, SourceLoc loc,
                          DiagEngine& diag) {
  std::vector<UwirePath>& earlier = nets_[declared];
  const bool kMeets = std::ranges::any_of(
      earlier, [&](const UwirePath& other) { return PathsMeet(other, path); });
  earlier.push_back(path);
  if (!kMeets) return;
  diag.ErrorOnce(loc,
                 std::format("uwire '{}' cannot have multiple drivers", name),
                 Subclause("6.6.2"));
}

UnitUwireCounts CountUnitUwireDrivers(const UnitUwireDrivers& units) {
  UnitUwireCounts counts;
  for (const auto& [unit, drivers] : units) {
    for (const auto& [net, paths] : drivers.Nets())
      counts[unit][net] = paths.size();
  }
  return counts;
}

// The drivers `drivers` recorded since `counts`, with the net each drives.
static std::vector<std::pair<std::string_view, UwirePath>> DriversSince(
    const UwireDrivers& drivers,
    const std::unordered_map<std::string_view, size_t>& counts) {
  std::vector<std::pair<std::string_view, UwirePath>> since;
  for (const auto& [net, paths] : drivers.Nets()) {
    auto count = counts.find(net);
    const size_t kFrom = count != counts.end() ? count->second : 0;
    for (size_t i = kFrom; i < paths.size(); ++i)
      since.emplace_back(net, paths[i]);
  }
  return since;
}

void RepeatUnitUwireDrivers(UnitUwireDrivers& units,
                            const UnitUwireCounts& counts, uint32_t elements,
                            SourceLoc loc, DiagEngine& diag) {
  if (elements <= 1) return;
  static const std::unordered_map<std::string_view, size_t> kNone;
  for (auto& [unit, drivers] : units) {
    auto unit_counts = counts.find(unit);
    // One more element already makes each of them a second driver.
    for (const auto& [net, path] :
         DriversSince(drivers, unit_counts != counts.end() ? unit_counts->second
                                                           : kNone))
      drivers.Record(net, net, path, loc, diag);
  }
}

// The indices the select `e` names in the dimension it selects: a bit or an
// element, a part between two bounds, or an indexed part from its base. Absent
// where a bound is not constant.
static std::optional<UwireStep> SelectStep(const Expr* e,
                                           const ScopeMap& constants) {
  std::optional<int64_t> index = ConstEvalInt(e->index, constants);
  if (!index) return std::nullopt;
  if (e->index_end == nullptr) return UwireStep{{}, *index, *index};
  std::optional<int64_t> end = ConstEvalInt(e->index_end, constants);
  if (!end) return std::nullopt;
  if (e->is_part_select_plus) return UwireStep{{}, *index, *index + *end - 1};
  if (e->is_part_select_minus) return UwireStep{{}, *index - *end + 1, *index};
  return UwireStep{{}, std::min(*index, *end), std::max(*index, *end)};
}

// The name `target` is rooted at, with `path` holding the steps from it down
// to what the target names, outermost first. Null where the target is rooted
// at no name or selects with a bound that is not constant.
static const Expr* RootAndPath(const Expr* target, const ScopeMap& constants,
                               UwirePath& path) {
  const Expr* e = target;
  while (e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess) {
    if (e->kind == ExprKind::kMemberAccess) {
      if (e->rhs == nullptr) return nullptr;
      path.push_back({e->rhs->text});
      e = e->lhs;
      continue;
    }
    std::optional<UwireStep> step = SelectStep(e, constants);
    if (!step) return nullptr;
    path.push_back(*step);
    e = e->base;
  }
  std::ranges::reverse(path);
  return e->kind == ExprKind::kIdentifier ? e : nullptr;
}

// Whether the scope has an object of its own named `name`, bound to
// `declared`: a variable or net, any other declaration, or a port.
static bool ScopeDeclares(std::string_view name, std::string_view declared,
                          const UwireTargetScope& in) {
  if (in.types.count(name) != 0 || in.names.declared.count(declared) != 0)
    return true;
  return std::ranges::any_of(
      in.mod->ports, [&](const RtlirPort& port) { return port.name == name; });
}

void RecordUwireTarget(UwireDrivers& drivers, const Expr* target, SourceLoc loc,
                       const UwireTargetScope& in, DiagEngine& diag) {
  if (target->kind == ExprKind::kConcatenation) {
    for (const Expr* element : target->elements)
      RecordUwireTarget(drivers, element, loc, in, diag);
    return;
  }
  UwirePath path;
  const Expr* root = RootAndPath(target, in.constants, path);
  if (root == nullptr) return;
  std::string_view name = root->text;
  std::string_view declared =
      DeclaredScopedName(name, in.names.scopes, in.names.declared);
  if (drivers.Declares(declared)) {
    drivers.Record(name, declared, path, loc, diag);
    return;
  }
  // §3.12.1: a name the scope does not declare is searched for in the part
  // of the compilation unit written before it.
  if (ScopeDeclares(name, declared, in)) return;
  const ModuleItem* net = UnitNetBefore(in.unit, name, loc);
  if (net == nullptr || WrittenNetType(net->data_type) != NetType::kUwire)
    return;
  in.unit_drivers[in.unit].Record(name, net->name, path, loc, diag);
}

void RecordUwirePrimitiveOutputs(UwireDrivers& drivers, const ModuleItem* item,
                                 const UwireTargetScope& in, DiagEngine& diag) {
  if (item->kind == ModuleItemKind::kGateInst) {
    GateType type = GateTypeOf(item->gate_kind);
    if (type == GateType::kPassSwitch || type == GateType::kPassEnSwitch)
      return;
  }
  // §28.3.6: an instance array gives each instance one bit of a terminal as
  // wide as the array, and connects any other terminal whole to every
  // instance, each of which then drives it; two of them are already more
  // drivers than one.
  const uint32_t kInstances =
      InstanceArrayLength(item, in.constants).value_or(1);
  for (const Expr* terminal : PrimitiveOutputTerminals(item)) {
    if (terminal == nullptr) continue;
    const bool kShared =
        kInstances > 1 &&
        GateTerminalWidth(terminal, in.mod, in.constants) != kInstances;
    RecordUwireTarget(drivers, terminal, item->loc, in, diag);
    if (kShared) RecordUwireTarget(drivers, terminal, item->loc, in, diag);
  }
}

}  // namespace delta
