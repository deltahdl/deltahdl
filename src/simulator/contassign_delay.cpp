#include "simulator/contassign_delay.h"

#include <algorithm>
#include <cstdint>
#include <optional>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_internal.h"

namespace delta {

static bool IsAllHighZ(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].aval != 0 || v.words[i].bval == 0) return false;
  }
  return v.nwords > 0;
}

// Whether a value with no x or z bit is zero, read across every word: a
// vector wider than one word may hold its only set bit above the first.
static bool IsKnownZero(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].aval != 0) return false;
  }
  return true;
}

static uint64_t SelectScalarContAssignDelay(const Logic4Vec& old_val,
                                            const Logic4Vec& new_val,
                                            const ContAssignDelays& d) {
  bool new_has_x = HasUnknownBits(new_val);
  if (new_has_x) {
    uint64_t m = std::min(d.rise, d.fall);
    if (d.has_decay) m = std::min(m, d.decay);
    return m;
  }
  if (HasUnknownBits(old_val) || IsAllHighZ(old_val)) {
    // Old value is x or z, new value is a known 0 or 1. The destination
    // logic level selects the slot: 0 routes through the fall delay and 1
    // through the rise delay, matching the x/z-source rows of Table 28-9.
    return new_val.ToUint64() == 0 ? d.fall : d.rise;
  }
  uint64_t nv = new_val.ToUint64();
  uint64_t ov = old_val.ToUint64();
  if (nv > ov) return d.rise;
  if (nv < ov) return d.fall;
  return d.rise;
}

// §10.3.3 decides which of the three delays governs, and for a vector net it
// decides it once for the assignment rather than once per bit: a vector net
// target admits up to three delays, the fall delay applying when the right-hand
// side goes from nonzero to zero, the turn-off delay when it goes to z, and the
// rise delay in every other case. Each rule reads the right-hand side whole, so
// a vector whose bits move in opposite directions is neither a transition to
// zero nor one to z, and the rising delay carries every bit of it: the whole
// vector settles at one time, not each bit at its own.
//
// The clause's later sentence restricts the same thing again for one of the two
// forms -- an assignment made in a vector net's declaration does not apply its
// rise and fall delays bit by bit -- and grants nothing to the other. A net
// delay is selected by these same rules for the net's own transition
// (Net::delay), so both forms settle a vector whole, which is what #3372 asked
// to be decided and recorded.
//
// A scalar left-hand side is the other half of the clause: its delay is handled
// as a gate delay is, which is Table 28-9 and is what
// SelectScalarContAssignDelay above reads.
uint64_t SelectContAssignDelay(const Logic4Vec& old_val,
                               const Logic4Vec& new_val,
                               const ContAssignDelays& d, uint32_t width) {
  if (!d.has_fall) return d.rise;

  bool new_is_z = IsAllHighZ(new_val);
  if (new_is_z) {
    if (d.has_decay) return d.decay;
    return std::min(d.rise, d.fall);
  }

  if (width <= 1) {
    return SelectScalarContAssignDelay(old_val, new_val, d);
  }

  if (!HasUnknownBits(new_val) && IsKnownZero(new_val) &&
      !HasUnknownBits(old_val) && !IsAllHighZ(old_val) &&
      !IsKnownZero(old_val)) {
    return d.fall;
  }
  return d.rise;
}

// An assignment to a concatenation is lowered as one assignment per element,
// each fed its slice of the source, and each keeps the declaration it came
// from as its source_item, whose target is the concatenation as written.
ContAssignWhole WholeOfConcatElement(const RtlirContAssign& ca) {
  const ModuleItem* item = ca.source_item;
  if (item == nullptr || item->kind != ModuleItemKind::kContAssign ||
      item->assign_lhs->kind != ExprKind::kConcatenation) {
    return {};
  }
  return {item->assign_lhs, item->assign_rhs};
}

// §10.3.3 makes the delay the time between a change of the source and the one
// assignment made to the target, and picks it from the source's transition as
// a whole. Picked by each element from its own slice, `#(5, 10) {a, b}` going
// from 8'h01 to 8'h10 gave a its rise delay and b its fall delay, and the
// target held 8'h11 between the two.
uint64_t SelectTransitionDelay(const ContAssignWhole& whole,
                               const ContAssignTransition& own,
                               const ContAssignDelays& d, SimContext& ctx,
                               Arena& arena) {
  if (whole.lhs == nullptr)
    return SelectContAssignDelay(own.old_val, own.new_val, d, own.width);
  Logic4Vec old_val = EvalExpr(whole.lhs, ctx, arena);
  Logic4Vec new_val = EvalExpr(whole.rhs, ctx, arena, old_val.width);
  return SelectContAssignDelay(old_val, new_val, d, old_val.width);
}

std::optional<ContAssignDelays> NetDelayTicks(const RtlirNet& net,
                                              const TimeScale& scale,
                                              SimContext& ctx, Arena& arena) {
  if (net.delay_rise == nullptr) return std::nullopt;
  auto ticks = [&](const Expr* e) {
    return DelayExprToTicksIn(e, scale, ctx, arena);
  };
  ContAssignDelays d;
  d.rise = ticks(net.delay_rise);
  d.has_fall = net.delay_fall != nullptr;
  d.fall = d.has_fall ? ticks(net.delay_fall) : 0;
  d.has_decay = net.delay_turnoff != nullptr;
  d.decay = d.has_decay ? ticks(net.delay_turnoff) : 0;
  return d;
}

}  // namespace delta
