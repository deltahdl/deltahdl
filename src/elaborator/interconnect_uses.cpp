#include "elaborator/interconnect_uses.h"

#include <algorithm>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

using InterconnectNames = std::unordered_set<std::string_view>;

bool IsInterconnectNetLvalue(const Expr* e, const InterconnectNames& names) {
  if (e == nullptr || e->is_parenthesized) return false;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      return names.count(e->text) != 0;
    case ExprKind::kSelect:
      return !ExprUsesInterconnect(e->index, names) &&
             !ExprUsesInterconnect(e->index_end, names) &&
             IsInterconnectNetLvalue(e->base, names);
    case ExprKind::kConcatenation:
    case ExprKind::kAssignmentPattern:
      return !e->elements.empty() &&
             std::ranges::all_of(e->elements, [&](const Expr* element) {
               return IsInterconnectNetLvalue(element, names);
             });
    default:
      return false;
  }
}

// A connection that names no interconnect is no concern of §6.6.8's, and one
// that does is legal only as an all-interconnect net_lvalue.
static bool ConnectionIsLegal(const Expr* e, const InterconnectNames& names) {
  return !ExprUsesInterconnect(e, names) || IsInterconnectNetLvalue(e, names);
}

// The expressions of an instance that connect nothing: its parameter values,
// its delays and the bounds of its instance array, in which an interconnect
// has no place at all.
static bool ValuesUseInterconnect(const ModuleItem& item,
                                  const InterconnectNames& names) {
  const Expr* const kValues[] = {item.gate_delay, item.gate_delay_fall,
                                 item.gate_delay_decay, item.inst_range_left,
                                 item.inst_range_right};
  auto uses = [&](const Expr* e) { return ExprUsesInterconnect(e, names); };
  return std::ranges::any_of(kValues, uses) ||
         std::ranges::any_of(item.inst_params,
                             [&](const auto& p) { return uses(p.second); }) ||
         std::ranges::any_of(item.inst_dims, [&](const auto& dim) {
           return uses(dim.first) || uses(dim.second);
         });
}

void ReportInterconnectInInstance(const ModuleItem& item,
                                  const InterconnectNames& names,
                                  DiagEngine& diag) {
  if (names.empty()) return;
  auto legal = [&](const Expr* e) { return ConnectionIsLegal(e, names); };
  const bool kConnectionsLegal =
      std::ranges::all_of(item.gate_terminals, legal) &&
      std::ranges::all_of(item.inst_ports,
                          [&](const auto& port) { return legal(port.second); });
  if (kConnectionsLegal && !ValuesUseInterconnect(item, names)) return;
  diag.Error(item.loc, "interconnect net cannot be used in expression",
             Subclause("6.6.8"));
}

}  // namespace delta
