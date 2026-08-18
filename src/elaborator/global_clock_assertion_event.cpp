#include "elaborator/global_clock_assertion_event.h"

#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

bool IsGlobalClockLeadingEvent(const std::vector<EventExpr>& sensitivity) {
  if (sensitivity.size() != 1) return false;
  const Expr* signal = sensitivity.front().signal;
  return signal != nullptr && signal->kind == ExprKind::kSystemCall &&
         signal->callee == "$global_clock";
}

bool SubstituteGlobalClockLeadingEvent(
    std::vector<EventExpr>& sensitivity,
    const std::vector<EventExpr>& global_event) {
  if (global_event.empty()) return false;
  if (!IsGlobalClockLeadingEvent(sensitivity)) return false;
  Expr* gate = sensitivity.front().iff_condition;
  sensitivity = global_event;
  for (auto& ev : sensitivity) {
    if (ev.iff_condition == nullptr) ev.iff_condition = gate;
  }
  return true;
}

}  // namespace delta
