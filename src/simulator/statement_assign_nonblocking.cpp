#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// §11.4.14: a deferred nonblocking write being installed onto `event`. Bundles
// the target variable, the sampled right-hand value, and the arena used by the
// update callback so the bit/part/whole select setup helpers share one entity.
struct NbaWrite {
  Event* event;
  Variable* var;
  const Logic4Vec& rhs_val;
  Arena& arena;
};

// §11.4.14: the NBA scheduling slot a deferred write lands in (the resolved
// region and the post-delay simulation time) together with the evaluation
// context. Shared by the array-concatenation and queue NBA scheduling paths.
struct NbaScheduleSlot {
  SimTime time;
  Region region;
  SimContext& ctx;
  Arena& arena;
};

static void SetupWholeVarNbaCallback(Event* event, Variable* var,
                                     const Logic4Vec& rhs_val);

// Append the elements of array `info` named `base` (in declared order) to
// `elems`. Missing element variables are skipped, matching a sparse store.
static void AppendArrayElements(std::string_view base, const ArrayInfo* info,
                                SimContext& ctx,
                                std::vector<Logic4Vec>& elems) {
  for (uint32_t i = 0; i < info->size; ++i) {
    uint32_t idx =
        info->is_descending ? (info->lo + info->size - 1 - i) : (info->lo + i);
    auto name = std::string(base) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    if (v) elems.push_back(v->value);
  }
}

// Expand a single identifier `item` of an array-concatenation rhs: array
// identifiers contribute their elements, queue identifiers splice their
// elements. Returns false when `item` is not an array/queue identifier.
static bool TryAppendConcatIdentifier(const Expr* item, SimContext& ctx,
                                      std::vector<Logic4Vec>& elems) {
  if (item->kind != ExprKind::kIdentifier) return false;
  if (auto* src_arr = ctx.FindArrayInfo(item->text)) {
    AppendArrayElements(item->text, src_arr, ctx, elems);
    return true;
  }
  if (auto* src_q = ctx.FindQueue(item->text)) {
    elems.insert(elems.end(), src_q->elements.begin(), src_q->elements.end());
    return true;
  }
  return false;
}

// Flatten the elements of an unpacked-array concatenation rhs into `elems`:
// array identifiers expand to their elements (in declared order), queue
// identifiers splice their elements, anything else evaluates as a scalar.
static void CollectArrayConcatElements(const Expr* rhs, SimContext& ctx,
                                       Arena& arena,
                                       std::vector<Logic4Vec>& elems) {
  for (auto* item : rhs->elements) {
    if (TryAppendConcatIdentifier(item, ctx, elems)) continue;
    elems.push_back(EvalExpr(item, ctx, arena));
  }
}

// Schedule the per-element NBA writes for an unpacked-array concatenation
// target. Reports a size mismatch (and stops) when element counts differ.
static void ScheduleArrayConcatNbaElements(const Stmt* stmt,
                                           const ArrayInfo* ainfo,
                                           const std::vector<Logic4Vec>& elems,
                                           const NbaScheduleSlot& slot) {
  if (elems.size() != ainfo->size) {
    slot.ctx.GetDiag().Error(
        {}, "unpacked array concatenation size mismatch: expected " +
                std::to_string(ainfo->size) + " elements, got " +
                std::to_string(elems.size()));
    return;
  }
  for (uint32_t i = 0; i < ainfo->size; ++i) {
    uint32_t idx = ainfo->is_descending ? (ainfo->lo + ainfo->size - 1 - i)
                                        : (ainfo->lo + i);
    auto name = std::string(stmt->lhs->text) + "[" + std::to_string(idx) + "]";
    auto* var = slot.ctx.FindVariable(name);
    if (!var) continue;
    auto val = ResizeToWidth(elems[i], ainfo->elem_width, slot.arena);
    auto* event = slot.ctx.GetScheduler().GetEventPool().Acquire();
    SetupWholeVarNbaCallback(event, var, val);
    slot.ctx.GetScheduler().ScheduleEvent(slot.time, slot.region, event);
  }
}

static bool TryArrayConcatNba(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) return false;
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kConcatenation) return false;

  auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
  auto* q = ctx.FindQueue(stmt->lhs->text);
  if (!ainfo && !q) return false;

  std::vector<Logic4Vec> elems;
  CollectArrayConcatElements(stmt->rhs, ctx, arena, elems);

  uint64_t delay = 0;
  if (stmt->delay) delay = EvalExpr(stmt->delay, ctx, arena).ToUint64();
  auto nba_region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  NbaScheduleSlot slot{ctx.CurrentTime() + SimTime{delay}, nba_region, ctx,
                       arena};

  if (ainfo) {
    ScheduleArrayConcatNbaElements(stmt, ainfo, elems, slot);
  } else {
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();

    event->kind = EventKind::kUpdate;
    event->callback = [q, elems = std::move(elems)]() {
      q->elements = elems;
      q->element_ids.clear();
      ++q->generation;
    };
    ctx.GetScheduler().ScheduleEvent(slot.time, slot.region, event);
  }
  return true;
}

StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (TryArrayConcatNba(stmt, ctx, arena)) return StmtResult::kDone;

  auto rhs_val = EvalRhsWithStructContext(stmt, ctx, arena);
  rhs_val = ApplyStreamPackToTargetWidening(stmt, rhs_val, ctx, arena);

  uint64_t delay = 0;
  if (stmt->delay) delay = EvalExpr(stmt->delay, ctx, arena).ToUint64();
  ScheduleNonblockingAssign(stmt, rhs_val, delay, ctx, arena);
  return StmtResult::kDone;
}

static void SetupWholeVarNbaCallback(Event* event, Variable* var,
                                     const Logic4Vec& rhs_val) {
  event->kind = EventKind::kUpdate;
  // Record the most recently scheduled pending value so the class garbage
  // collector can keep a handle awaiting an NBA update reachable (see the
  // pending_nba scan in the class GC).
  var->pending_nba = rhs_val;
  var->has_pending_nba = true;
  // §10.4.2: each scheduled nonblocking update carries its own sampled
  // right-hand value and applies it at its own scheduled time. When several
  // intra-assignment-delayed NBAs target the same variable at distinct future
  // times (Example 7), they must not cancel one another, so the update value
  // is captured here rather than read from the single shared pending_nba slot.
  event->callback = [var, rhs_val]() {
    if (!var->is_forced) {
      var->value = rhs_val;
      if (!var->is_4state) CoerceTo2State(var->value);
      var->NotifyWatchers();
    }
    var->has_pending_nba = false;
  };
}

// §11.4.14.3: a streaming_concatenation can be the target of a nonblocking
// assignment too, performing the same reverse (unpack) operation. The source
// is sampled now; defer the per-target writes to the NBA region so the
// streaming semantics match the blocking form.
static void ScheduleStreamingConcatNba(const Stmt* stmt,
                                       const Logic4Vec& rhs_val,
                                       uint64_t delay_ticks, SimContext& ctx,
                                       Arena& arena) {
  auto* stream_event = ctx.GetScheduler().GetEventPool().Acquire();
  stream_event->kind = EventKind::kUpdate;
  const Expr* lhs = stmt->lhs;
  stream_event->callback = [lhs, rhs_val, &ctx, &arena]() {
    UnpackStreamingConcatLhs(lhs, rhs_val, ctx, arena);
  };
  auto stream_region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  auto stream_time = ctx.CurrentTime() + SimTime{delay_ticks};
  ctx.GetScheduler().ScheduleEvent(stream_time, stream_region, stream_event);
}

// Install the deferred update callback for a single-bit NBA write of `idx`.
static void SetupBitSelectNbaCallback(const NbaWrite& write, uint32_t idx) {
  Variable* var = write.var;
  Logic4Vec rhs_val = write.rhs_val;
  Arena& arena = write.arena;
  write.event->callback = [var, idx, rhs_val, &arena]() {
    if (idx >= var->value.width) return;
    uint64_t old_val = var->value.ToUint64();
    uint64_t bit = rhs_val.ToUint64() & 1;
    uint64_t cleared = old_val & ~(uint64_t{1} << idx);
    var->value =
        MakeLogic4VecVal(arena, var->value.width, cleared | (bit << idx));
    var->NotifyWatchers();
  };
}

// Install the deferred update callback for a `w`-bit part-select NBA write
// starting at bit `lo`.
static void SetupPartSelectNbaCallback(const NbaWrite& write, uint32_t lo,
                                       uint32_t w) {
  Variable* var = write.var;
  Logic4Vec rhs_val = write.rhs_val;
  Arena& arena = write.arena;
  write.event->callback = [var, lo, w, rhs_val, &arena]() {
    uint64_t mask = (w >= 64) ? ~uint64_t{0} : (uint64_t{1} << w) - 1;
    uint64_t old_val = var->value.ToUint64();
    uint64_t new_bits = (rhs_val.ToUint64() & mask) << lo;
    uint64_t cleared = old_val & ~(mask << lo);
    var->value = MakeLogic4VecVal(arena, var->value.width, cleared | new_bits);
    var->NotifyWatchers();
  };
}

// §11.4.14 / §7.4.6: the resolved low bit and width of a part-select NBA
// target, clamped to the variable width.
struct PartSelectRange {
  uint32_t lo;
  uint32_t w;
};

// Resolve the [lo, w) part-select range for `lhs` given base index `idx` and
// `end_val`, mirroring the plus/minus/ranged select forms. Returns nullopt when
// the select has zero width or lies entirely outside `var_width`; otherwise
// clamps the range to the variable width.
static std::optional<PartSelectRange> ResolvePartSelectNbaRange(
    const Expr* lhs, uint32_t idx, uint32_t end_val, uint32_t var_width) {
  uint32_t lo = idx;
  uint32_t w = end_val;
  if (lhs->is_part_select_plus) {
  } else if (lhs->is_part_select_minus) {
    lo = (idx >= w - 1) ? idx - w + 1 : 0;
  } else {
    lo = std::min(idx, end_val);
    w = std::max(idx, end_val) - lo + 1;
  }
  if (w == 0 || lo >= var_width) return std::nullopt;
  if (lo + w > var_width) w = var_width - lo;
  return PartSelectRange{lo, w};
}

// Configure the deferred update callback for an NBA whose target is an
// unresolved bit-select or part-select of `var`. Returns false (without
// setting a callback) when the assignment must be dropped: an unknown index,
// or a part-select that resolves to zero width / falls entirely out of range.
static bool SetupSelectNbaCallback(const NbaWrite& write, const Expr* lhs,
                                   SimContext& ctx) {
  auto idx_val = EvalExpr(lhs->index, ctx, write.arena);
  if (HasUnknownBits(idx_val)) return false;
  auto idx = static_cast<uint32_t>(idx_val.ToUint64());

  if (!lhs->index_end) {
    SetupBitSelectNbaCallback(write, idx);
    return true;
  }

  uint32_t end_val = static_cast<uint32_t>(
      EvalExpr(lhs->index_end, ctx, write.arena).ToUint64());
  auto range =
      ResolvePartSelectNbaRange(lhs, idx, end_val, write.var->value.width);
  if (!range) return false;
  SetupPartSelectNbaCallback(write, range->lo, range->w);
  return true;
}

void ScheduleNonblockingAssign(const Stmt* stmt, const Logic4Vec& rhs_val,
                               uint64_t delay_ticks, SimContext& ctx,
                               Arena& arena) {
  if (!stmt->lhs) return;

  if (stmt->lhs->kind == ExprKind::kStreamingConcat) {
    ScheduleStreamingConcatNba(stmt, rhs_val, delay_ticks, ctx, arena);
    return;
  }

  bool is_select = (stmt->lhs->kind == ExprKind::kSelect);
  auto* elem = is_select ? TryResolveArrayElement(stmt->lhs, ctx) : nullptr;
  auto* var = elem ? elem : ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return;

  auto* event = ctx.GetScheduler().GetEventPool().Acquire();

  event->kind = EventKind::kUpdate;
  if (is_select && !elem) {
    NbaWrite write{event, var, rhs_val, arena};
    if (!SetupSelectNbaCallback(write, stmt->lhs, ctx)) return;
  } else {
    auto converted =
        ConvertRealOnAssign(rhs_val, stmt->lhs, var->value.width, ctx, arena);
    SetupWholeVarNbaCallback(event, var, converted);
  }
  auto nba_region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  auto schedule_time = ctx.CurrentTime() + SimTime{delay_ticks};
  ctx.GetScheduler().ScheduleEvent(schedule_time, nba_region, event);
}

}  // namespace delta
