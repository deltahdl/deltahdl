#include <cmath>
#include <cstdint>
#include <format>
#include <optional>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "parser/ast_expr.h"

namespace delta {

namespace {

void CheckOneDelay(const Expr* delay, const ScopeMap& scope, DiagEngine& diag) {
  if (delay == nullptr) return;
  std::optional<int64_t> value = ConstEvalInt(delay, scope);
  if (!value.has_value()) {
    if (auto real_value = ConstEvalReal(delay, scope)) {
      value = std::llround(*real_value);
    }
  }
  if (!value.has_value() || *value >= 0) return;
  diag.Error(delay->range.start,
             std::format("delay is {}; a delay is the time between two events "
                         "and has no negative value",
                         *value),
             Subclause("28.16"));
}

void CheckDelay(const Expr* delay, const ScopeMap& scope, DiagEngine& diag) {
  if (delay == nullptr) return;
  if (delay->kind == ExprKind::kMinTypMax) {
    CheckOneDelay(delay->lhs, scope, diag);
    CheckOneDelay(delay->condition, scope, diag);
    CheckOneDelay(delay->rhs, scope, diag);
    return;
  }
  CheckOneDelay(delay, scope, diag);
}

}  // namespace

bool ItemCarriesDelay(const ModuleItem* item) {
  return item != nullptr &&
         (item->net_delay != nullptr || item->net_delay_fall != nullptr ||
          item->net_delay_decay != nullptr || item->assign_delay != nullptr ||
          item->assign_delay_fall != nullptr ||
          item->assign_delay_decay != nullptr || item->gate_delay != nullptr ||
          item->gate_delay_fall != nullptr ||
          item->gate_delay_decay != nullptr);
}

void ValidateItemDelaysNonNegative(const ModuleItem* item,
                                   const ScopeMap& scope, DiagEngine& diag) {
  CheckDelay(item->net_delay, scope, diag);
  CheckDelay(item->net_delay_fall, scope, diag);
  CheckDelay(item->net_delay_decay, scope, diag);
  CheckDelay(item->assign_delay, scope, diag);
  CheckDelay(item->assign_delay_fall, scope, diag);
  CheckDelay(item->assign_delay_decay, scope, diag);
  CheckDelay(item->gate_delay, scope, diag);
  CheckDelay(item->gate_delay_fall, scope, diag);
  CheckDelay(item->gate_delay_decay, scope, diag);
}

}  // namespace delta
