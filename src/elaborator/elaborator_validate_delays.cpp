#include <cmath>
#include <format>
#include <optional>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "parser/ast.h"

namespace delta {

namespace {

// §28.16: a delay is a duration between two moments, taken in that order -- a
// net delay is "the time it takes from any driver on the net changing value to
// the time when the net value is updated and propagated further", and §28.16.2
// gives a trireg's charge decay time as "the delay between when the drivers of
// a trireg net turn off and when its stored charge can no longer be
// determined". No form the clause gives a delay runs backwards, so a delay that
// folds to a negative value is a source the standard does not describe.
//
// A delay that does not fold is not reported. It may name a parameter this
// scope cannot see, and what value it will have is not this pass's to settle;
// only a value the pass can compute and see to be negative is a breach.
void CheckOneDelay(const Expr* delay, const ScopeMap& scope, DiagEngine& diag) {
  if (delay == nullptr) return;
  std::optional<int64_t> value = ConstEvalInt(delay, scope);
  if (!value.has_value()) {
    // A.2.2.3 admits a real_number as a delay_value, which ConstEvalInt does
    // not fold. §3.14.1 rounds a delay value to the precision before it is
    // used, so the sign of what a real delay becomes is the sign of the value
    // written, and a negative one is as much a breach as a negative integer.
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

// §28.16.1: a delay may be written as three expressions -- "The minimum,
// typical, and maximum values for each delay shall be specified as expressions
// separated by colons ... These can be any three expressions" -- and which of
// them is the delay is settled per run rather than per source. Each is the
// delay in some run, so each is checked; reading only the folded scalar would
// see whichever member the active mode selects and pass the other two.
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
  // Every delay this item can carry, rather than the one slot a wrap was first
  // seen through: §28.16 states one rule over the delays of nets, gates,
  // primitives and continuous assignments, and a check on one of them would
  // leave the rest reading as an oversight. The net's three slots are the
  // rise, the fall and -- on a trireg, per §28.16.2.2 -- the charge decay time;
  // the other six are the continuous assignment's and the gate or primitive
  // instance's.
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
