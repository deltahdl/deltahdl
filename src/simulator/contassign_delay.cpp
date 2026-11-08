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
    return new_val.ToUint64() == 0 ? d.fall : d.rise;
  }
  uint64_t nv = new_val.ToUint64();
  uint64_t ov = old_val.ToUint64();
  if (nv > ov) return d.rise;
  if (nv < ov) return d.fall;
  return d.rise;
}

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

ContAssignWhole WholeOfConcatElement(const RtlirContAssign& ca) {
  const ModuleItem* item = ca.source_item;
  if (item == nullptr || item->kind != ModuleItemKind::kContAssign ||
      item->assign_lhs->kind != ExprKind::kConcatenation) {
    return {};
  }
  return {item->assign_lhs, item->assign_rhs};
}

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
