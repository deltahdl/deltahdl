#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/queue_bound.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// §11.4.14: a deferred nonblocking write being installed onto `event`. Bundles
// the target variable, the sampled right-hand value, and the arena used by the
// update callback so the select and whole-variable setup helpers share one
// entity.
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
        stmt->range.start,
        "unpacked array concatenation size mismatch: expected " +
            std::to_string(ainfo->size) + " elements, got " +
            std::to_string(elems.size()),
        Subclause("10.10"));
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

// §7.10.4: a right-hand side that gives a queue its elements rather than one
// value. The subclause writes those as an unpacked array concatenation, as in
// `q = {q, 6}`, and as a bare slice of a queue, as in `q = q[1:$]`. The second
// carries no braces, so a test for a concatenation alone reads it as the single
// value its elements would concatenate to and leaves the queue holding one
// element where the slice named several.
static bool IsQueueValuedRhs(const Expr* rhs, SimContext& ctx) {
  if (rhs->kind == ExprKind::kConcatenation) return true;
  if (rhs->kind != ExprKind::kSelect || !rhs->base || !rhs->index_end)
    return false;
  return rhs->base->kind == ExprKind::kIdentifier &&
         ctx.FindQueue(rhs->base->text) != nullptr;
}

static bool TryArrayConcatNba(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier || !stmt->rhs)
    return false;

  auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
  auto* q = ainfo ? nullptr : ctx.FindQueue(stmt->lhs->text);
  if (!ainfo && !q) return false;
  if (ainfo && stmt->rhs->kind != ExprKind::kConcatenation) return false;
  if (q && !IsQueueValuedRhs(stmt->rhs, ctx)) return false;

  // §10.4.2 evaluates the right-hand side of a nonblocking assignment when the
  // statement executes, so the elements are collected here and the event
  // installs the value they made. A right-hand side naming the target queue
  // therefore reads what the queue held at execution, as §7.10.4's `q = q[1:$]`
  // requires.
  std::vector<Logic4Vec> elems;
  if (ainfo) {
    CollectArrayConcatElements(stmt->rhs, ctx, arena, elems);
  } else {
    CollectQueueElements(stmt->rhs, ctx, arena, elems);
  }

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
    event->callback = [q, &ctx, loc = stmt->rhs->range.start,
                       elems = std::move(elems)]() {
      q->elements = elems;
      EnforceQueueBound(q, "nonblocking assignment", loc, ctx);
      // §7.10.3: assigning the queue variable outdates every reference to the
      // elements it held. Fresh ids do that, where clearing the list would also
      // stop the queue recording a reference taken after the assignment, which
      // the subclause outdates nothing of.
      q->AssignFreshIds();
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
// §11.4.12: "The concatenation is treated as a packed vector of bits. It can be
// used on the left-hand side of an assignment", and §10.9 gives an assignment
// pattern the same use. §10.4.2 gives the nonblocking form the same
// variable_lvalue the blocking form takes -- "variable_lvalue is a data type
// that is valid for a procedural assignment statement" -- so a concatenation is
// a nonblocking target exactly as it is a blocking one, and `{a, b} <= x` has
// to distribute where `{a, b} = x` does.
//
// The distribution is the blocking one, deferred rather than restated: one
// event carries the sampled right-hand value and runs TryUnpackConcatLhs in the
// update region, as the streaming arm below carries its own unpacker. Resolving
// the elements here instead and scheduling a whole-variable write for each
// cannot answer for the forms that unpacker handles -- a nested concatenation
// names no variable to write, and a select element resolves to the whole of the
// variable it selects from, which is the boundary error ConcatLhsElemWidth
// records having already been made once on the blocking side.
static void ScheduleConcatNba(const Stmt* stmt, const Logic4Vec& rhs_val,
                              uint64_t delay_ticks, SimContext& ctx,
                              Arena& arena) {
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->kind = EventKind::kUpdate;
  const Expr* lhs = stmt->lhs;
  event->callback = [lhs, rhs_val, &ctx, &arena]() {
    TryUnpackConcatLhs(lhs, rhs_val, ctx, arena);
  };
  auto region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime() + SimTime{delay_ticks},
                                   region, event);
}

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

// §11.5.1: install the deferred update that deposits the sampled right-hand
// value in the window `bits` names -- the bits of the target the select
// addresses, and where in the value the bits they receive begin. The window is
// already resolved when this is called; see SetupSelectNbaCallback below for
// why it is resolved there and not here.
static void SetupPartSelectNbaCallback(const NbaWrite& write,
                                       const PartSelectBits& bits) {
  Variable* var = write.var;
  Logic4Vec rhs_val = write.rhs_val;
  Arena& arena = write.arena;
  write.event->callback = [var, bits, rhs_val, &arena]() {
    // §10.6.2: a force "shall override a procedural assignment ... until a
    // release procedural statement is executed on the variable", and §10.4
    // names a nonblocking assignment as one of the three kinds of procedural
    // assignment whatever its left-hand side is. The check sits inside the
    // callback rather than where the event was scheduled, as it does in
    // SetupWholeVarNbaCallback, because the flag that governs the write is the
    // one standing when the update region runs and not when it was queued.
    // WritePartSelect itself does not ask -- its blocking caller WriteBitSelect
    // asks before it evaluates the indices, which is the wrong moment here --
    // so this is where a forced target is declined.
    if (var->is_forced) return;
    WritePartSelect(var, bits, rhs_val, arena);
    var->NotifyWatchers();
  };
}

// Configure the deferred update callback for a nonblocking assignment whose
// left-hand side is a bit-select or a part-select of `write.var`. Returns
// false, having installed no callback, when the select addresses no bit of the
// object and the assignment is therefore dropped: §11.5.1 has a write through
// an index carrying x or z, and one through an address wholly outside the
// declared bounds, "have no effect on the data stored", which is a zero width
// from SelectStorageBits.
//
// One installer answers both select forms because SelectStorageBits answers
// both: an ordinary bit-select is the one-bit window its declared range gives
// the index (Variable::BitSelectRange), and a single index of a packed
// multidimensional array addresses that array's element rather than one bit
// (§7.4.1), whose window is as wide as the element. A separate bit-select
// installer stood here and tested `idx >= var->value.width`, reading the index
// as a storage offset, so on a `logic [15:8] a` -- eight bits of storage
// addressed by the indices 8 through 15 -- every nonblocking bit-select write
// was dropped.
//
// §11.5.1 is stated once, by SelectStorageBits and WritePartSelect, rather than
// twice. The copy that stood here computed its window in uint32_t against
// `var->value.width` alone and predated three corrections to that shared
// arithmetic. It read §5.7.1's signed decimal `-2` as 4294967294, so on a
// `logic [7:0] a` the write `a[1:-2] <= 4'b1101` left 8'h1A where the clause
// requires 8'h03. It carried no source offset, so a select running off the low
// end took the value's least significant bits, and `a[1 -: 4] <= 4'b1101` on
// the same variable left 8'h0D where that same 8'h03 is required -- §11.5.1
// reads the indexed form as `a[1:-2]`, whose most significant end is index 1,
// so `a[1]` takes the value's bit 3 and `a[0]` its bit 2. And it read an index
// as a storage offset rather than resolving it against the declaration, so on a
// `logic [15:8] a` the write `a[9:8] <= 2'b11` was dropped whole.
//
// The resolution is asked here, where the event is scheduled, and not from
// inside the callback, because §10.4.2 evaluates the left-hand side's index
// expressions along with the right-hand side when the statement executes. Only
// the arithmetic moved into the shared helpers; when it runs is unchanged.
static bool SetupSelectNbaCallback(const NbaWrite& write, const Expr* lhs,
                                   SimContext& ctx) {
  PartSelectBits bits = SelectStorageBits(*write.var, lhs, ctx, write.arena);
  if (bits.width == 0) return false;
  SetupPartSelectNbaCallback(write, bits);
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
  // The gate is asked before an event is taken from the pool, rather than by
  // letting the unpacker decline inside the callback, which would spend one on
  // every left-hand side that is not a concatenation.
  if (IsConcatLhs(stmt->lhs)) {
    ScheduleConcatNba(stmt, rhs_val, delay_ticks, ctx, arena);
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
    // §11.5.1 makes a select that addresses no bit of its object -- one whose
    // index carries x or z, and one whose address lies wholly outside the
    // declared bounds -- "have no effect on the data stored when written", so
    // declining the write is the clause rather than an error, and only the
    // bookkeeping was wrong. The event is taken from the pool before the window
    // is resolved because NbaWrite carries the Event* the installer writes its
    // callback onto, so the one this path does not use is handed back here.
    // EventPool::Release (scheduler.cpp:22) resets kind, target, callback and
    // superseded before relinking, so an event returned mid-setup is as clean
    // as one the scheduler drains from a queue, and SetupSelectNbaCallback
    // installs no callback on the path that returns false, so there is nothing
    // else to undo. Returning without it lost the event for the rest of the
    // run: the arena has no per-object free, and every other route back to the
    // pool runs on an event that reached a queue.
    if (!SetupSelectNbaCallback(write, stmt->lhs, ctx)) {
      ctx.GetScheduler().GetEventPool().Release(event);
      return;
    }
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
