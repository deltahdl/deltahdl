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
#include "simulator/clocking.h"
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

// Hands `event` to the scheduler as a nonblocking update: the NBA region, or
// the reactive one when the statement runs in a reactive context, at the time
// an intra-assignment delay of `delay_ticks` puts it. The schedulers below
// differ in the callback they install and not in where the event goes, so
// where it goes is stated once.
static void ScheduleNbaEvent(Event* event, uint64_t delay_ticks,
                             SimContext& ctx) {
  auto region = ctx.IsReactiveContext() ? Region::kReNBA : Region::kNBA;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime() + SimTime{delay_ticks},
                                   region, event);
}

// §4.9.4: "The values in effect when the update is placed in the event
// region are used to compute both the right-hand value and the left-hand
// target." EvalExpr on a bare identifier hands back the variable's own vec
// (evaluation.cpp), and copying a Logic4Vec copies its `words` pointer rather
// than the words (common/types.h), so a sampled right-hand value aliases the
// storage it was read from. A whole-variable write replaces that storage and
// cannot be seen through the alias, but an in-place writer reaches through it
// and changes what a pending update will store: the packed struct member
// deposit WriteResolvedField makes (statement_assign.cpp) left
// `s = 16'hAABB; d <= s; s.b = 8'h00;` storing 16'h00BB, and the CoerceTo2State
// in SetupWholeVarNbaCallback below writes through the alias in the other
// direction, clearing the source variable's x and z bits when the target is
// 2-state.
//
// The copy is taken once, where the value is sampled, so every capture
// downstream already owns its words. A Logic4Snapshot is the wrong tool for it
// even though it is the right one for the lvalue index snapshots below: a
// snapshot's storage is a member of the snapshot object, so a callback doing
// `var->value = snap.Get()` would leave the variable pointing at words that
// die with the lambda. Those index snapshots are read and discarded inside the
// callback body; this value has to outlive the callback, which is what the
// arena gives it.
//
// ExtractBitField copies the bits -- multi-word safe and 4-state preserving --
// but builds its result with MakeLogic4Vec, which leaves is_real, is_signed
// and is_string at their defaults. Those are read downstream, where
// ConvertRealForKnownLhs converts across the §6.12.1 real boundary on is_real
// and ResizeToWidth sign-extends on is_signed, so they are carried over here.
static Logic4Vec SampleNbaRhs(const Logic4Vec& val, Arena& arena) {
  Logic4Vec copy = ExtractBitField(arena, val, 0, val.width);
  copy.is_real = val.is_real;
  copy.is_signed = val.is_signed;
  copy.is_string = val.is_string;
  return copy;
}

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

// Replace each collected element with a copy that owns its words. Every
// collector pushes a variable's own vec or a queue's own elements, so every
// entry arrives aliasing live storage. Copying here rather than inside each
// collector reaches the queue splice and CollectQueueElements
// (statement_assign_pattern.cpp) as well, and asks no collector for an arena.
static void SampleConcatElements(std::vector<Logic4Vec>& elems, Arena& arena) {
  for (auto& elem : elems) elem = SampleNbaRhs(elem, arena);
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
  SampleConcatElements(elems, arena);

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
  // Every capture reached through ScheduleNonblockingAssign flows from here, so
  // one copy at the point of sampling covers all of them.
  rhs_val = SampleNbaRhs(rhs_val, arena);

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

// §10.4.2: "If the variable_lvalue requires an evaluation, such as an index
// expression, class handle, or virtual interface reference, it shall be
// evaluated at the same time as the expression on the right-hand side", and
// §4.9.4 has the values in effect when the update is placed in the event
// region compute "both the right-hand value and the left-hand target". The two
// brace arms below defer the write itself, which is where the write belongs --
// resolving the elements at schedule time cannot answer for the forms their
// unpackers handle -- but their unpackers evaluate the lvalue's index
// expressions where they run, which is the update region. So `{a[idx], b} <= x`
// read whatever `idx` held when the update fired rather than what it held when
// the statement executed. These pair each index node under a left-hand side
// with the value it has now, for the callback to install as the
// deferred-argument snapshots EvalExpr consults before evaluating anything.
// The value is held in a Logic4Snapshot rather than a Logic4Vec because a
// Logic4Vec copy keeps pointing at the words it was copied from, and a write
// does not always replace the words it writes -- the trap variable.h records
// for #3358, where both sides of a comparison became one value. A snapshot
// owns its words, so an in-place write to the object an index expression read
// cannot reach back into what was sampled for the event still pending.
using LhsIndexSnapshots = std::vector<std::pair<const Expr*, Logic4Snapshot>>;

// Pair `node` with its value now, when there is a node to pair. A constant
// index is paired like any other: it re-evaluates to the same value, so the
// snapshot costs one entry and asks the walk no question about the expression.
static void CollectIndexSnapshot(const Expr* node, SimContext& ctx,
                                 Arena& arena, LhsIndexSnapshots& out) {
  if (!node) return;
  out.emplace_back();
  out.back().first = node;
  out.back().second.Capture(EvalExpr(node, ctx, arena));
}

static void CollectLhsIndexSnapshotsInto(const Expr* lhs, SimContext& ctx,
                                         Arena& arena, LhsIndexSnapshots& out);

// The indices of a select: its own, and then those of its base, since §7.4.5's
// indexed name can name a select of a select.
static void CollectSelectIndices(const Expr* sel, SimContext& ctx, Arena& arena,
                                 LhsIndexSnapshots& out) {
  CollectIndexSnapshot(sel->index, ctx, arena, out);
  CollectIndexSnapshot(sel->index_end, ctx, arena, out);
  CollectLhsIndexSnapshotsInto(sel->base, ctx, arena, out);
}

// The indices under each element of a concatenation, an assignment pattern or a
// streaming concatenation. §11.4.14.3's `with` range is an index expression of
// the element it qualifies -- ResolveWithRange evaluates it -- so it is taken
// here alongside the element's own.
static void CollectElementIndices(const Expr* expr, SimContext& ctx,
                                  Arena& arena, LhsIndexSnapshots& out) {
  for (const auto* elem : expr->elements) {
    if (!elem) continue;
    if (elem->with_expr) {
      CollectIndexSnapshot(elem->with_expr->index, ctx, arena, out);
      CollectIndexSnapshot(elem->with_expr->index_end, ctx, arena, out);
    }
    CollectLhsIndexSnapshotsInto(elem, ctx, arena, out);
  }
}

static void CollectLhsIndexSnapshotsInto(const Expr* lhs, SimContext& ctx,
                                         Arena& arena, LhsIndexSnapshots& out) {
  if (!lhs) return;
  // §10.9's type prefix is a cast around the pattern, and a nested
  // concatenation is one of the forms UnpackConcatLhs walks, so the walk looks
  // through the prefix at every level rather than only at the top.
  const Expr* target = UnwrapTypedPattern(lhs);
  if (!target) return;
  switch (target->kind) {
    case ExprKind::kSelect:
      CollectSelectIndices(target, ctx, arena, out);
      break;
    case ExprKind::kConcatenation:
    case ExprKind::kAssignmentPattern:
    case ExprKind::kStreamingConcat:
      CollectElementIndices(target, ctx, arena, out);
      break;
    default:
      break;
  }
}

static LhsIndexSnapshots CollectLhsIndexSnapshots(const Expr* lhs,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  LhsIndexSnapshots out;
  CollectLhsIndexSnapshotsInto(lhs, ctx, arena, out);
  return out;
}

// The snapshots are installed for the length of one callback body and dropped
// again at its end. The store is one map per SimContext keyed by expression
// node -- not one per event and not one per process -- so holding them live
// from the statement through to the update region would let a second execution
// of the same statement (a loop body scheduling it twice in one time step, two
// processes or two instances running it, an intra-assignment delay whose
// statement re-executes before its update fires) overwrite the key an event
// still pending reads, and the first clear would empty the store for every
// event after it. Update-region callbacks run one at a time, so each installing
// its own values over the same keys is enough. The words the stash points at
// are the ones the captured vector owns, and the callback it is captured on is
// released only after it returns (Scheduler::DrainQueue), so every entry is
// cleared while the storage behind it is still standing.
static void InstallLhsIndexSnapshots(const LhsIndexSnapshots& snaps,
                                     SimContext& ctx) {
  for (const auto& snap : snaps) {
    ctx.SetDeferredArgSnapshot(snap.first, snap.second.Get());
  }
}

static void ClearLhsIndexSnapshots(const LhsIndexSnapshots& snaps,
                                   SimContext& ctx) {
  for (const auto& snap : snaps) ctx.ClearDeferredArgSnapshot(snap.first);
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
  auto snaps = CollectLhsIndexSnapshots(lhs, ctx, arena);
  event->callback = [lhs, rhs_val, snaps, &ctx, &arena]() {
    InstallLhsIndexSnapshots(snaps, ctx);
    TryUnpackConcatLhs(lhs, rhs_val, ctx, arena);
    ClearLhsIndexSnapshots(snaps, ctx);
  };
  ScheduleNbaEvent(event, delay_ticks, ctx);
}

static void ScheduleStreamingConcatNba(const Stmt* stmt,
                                       const Logic4Vec& rhs_val,
                                       uint64_t delay_ticks, SimContext& ctx,
                                       Arena& arena) {
  auto* stream_event = ctx.GetScheduler().GetEventPool().Acquire();
  stream_event->kind = EventKind::kUpdate;
  const Expr* lhs = stmt->lhs;
  auto snaps = CollectLhsIndexSnapshots(lhs, ctx, arena);
  stream_event->callback = [lhs, rhs_val, snaps, &ctx, &arena]() {
    InstallLhsIndexSnapshots(snaps, ctx);
    UnpackStreamingConcatLhs(lhs, rhs_val, ctx, arena);
    ClearLhsIndexSnapshots(snaps, ctx);
  };
  ScheduleNbaEvent(stream_event, delay_ticks, ctx);
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

// §10.4.2 gives the nonblocking form the same target the blocking form takes --
// `nonblocking_assignment ::= variable_lvalue <= [ delay_or_event_control ]
// expression`, where variable_lvalue "is a data type that is valid for a
// procedural assignment statement" -- so a select that names an element must
// reach the same object here as it does in TrySelectBlockingAssign, which asks
// these two resolvers in this order. §7.4.5: "A single element of a packed or
// unpacked array can be selected using an indexed name."
//
// TryResolveArrayElement answers only a one-dimensional indexed name, declining
// outright when the select's base is itself a select, so `A[1][2] <= 43` on an
// `int A[2][3]` fell through to the base variable `A` -- the element-width cell
// LowerVar registers under the declared name, which no element is stored in --
// and the select branch below read the element index 2 as a bit position and
// wrote one bit of it. TryResolveCompoundElement is entered on exactly that
// condition: it rebuilds the full indexed name and finds the leaf that
// CreateMultiDimLeaves made. Every route into ScheduleNonblockingAssign shares
// this resolution, so the event-controlled forms get it too.
//
// Both decline an lhs carrying an index_end, so a slice such as `A[1][1:2] <=
// x` still reaches the part-select callback. A packed sub-select of an unpacked
// element -- `logic [7:0] mem [0:3]; mem[0][3] <= 1'b1;` -- is not an element
// at all and is answered by neither: §11.5.1 makes it a bit of the element
// mem[0], so it is resolved by the caller through TryResolveCompoundElementBase
// and takes the select-window callback the same bit-select of a plain variable
// takes. Asking it there rather than here is what keeps that route open: an
// element answered from this function is written whole.
static Variable* ResolveNbaSelectElement(const Expr* lhs, SimContext& ctx,
                                         Arena& arena, bool* absent_element) {
  *absent_element = false;
  if (lhs->kind != ExprKind::kSelect) return nullptr;
  if (auto* elem = TryResolveArrayElement(lhs, ctx)) return elem;
  if (TryResolveCompoundElementBase(lhs, ctx, arena) != nullptr) return nullptr;
  return TryResolveCompoundElement(lhs, ctx, arena, absent_element);
}

// §10.4.2 gives the nonblocking form the same `variable_lvalue` the blocking
// form takes, and A.8.5 makes a dotted member path the first production of
// variable_lvalue, so a member of a packed struct and a property of a class
// object are nonblocking targets exactly as they are blocking ones. Neither is
// a key in the variable table -- a packed member is a window of bits inside one
// variable and a property lives on the ClassObject -- so ResolveLhsVariable
// answers nothing for either and the assignment was dropped in silence: no
// event, no write, no diagnostic.
//
// The target is resolved here, where the statement executes, and only the
// deposit is deferred, for the reason SetupSelectNbaCallback resolves a
// select's window here: §10.4.2 has an lvalue that "requires an evaluation,
// such as an index expression, class handle, or virtual interface reference"
// evaluated "at the same time as the expression on the right-hand side".
// Calling WriteStructField from the callback would satisfy the clause for
// neither, since it re-resolves the base itself -- `this` is a property of the
// running process, which in the update region is no longer the process that
// executed the statement, and the base handle is read from a variable that may
// have been assigned since.
//
// Nothing is taken from the event pool until the target resolves, so a path
// naming no storage -- a null handle, a `this` outside a method -- costs no
// event. §10.4.2 leaves nothing to write there, which is the answer the
// blocking form gives it too.
// §14.16's clockvar of a synchronous drive: the block a `cb.sig <= value`
// names and the signal within it, or nothing where the left-hand side is not a
// clockvar at all. The clause writes the target as `clockvar_expression ::=
// clockvar select` with `clockvar ::= hierarchical_identifier`, so the base
// names the block and the member names the signal.
static const ClockingSignal* FindClockvarSignal(const Expr* lhs,
                                                SimContext& ctx,
                                                std::string_view* block_name) {
  if (lhs->kind != ExprKind::kMemberAccess) return nullptr;
  if (lhs->lhs == nullptr || lhs->lhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  auto* mgr = ctx.GetClockingManager();
  if (mgr == nullptr) return nullptr;
  const ClockingBlock* block = mgr->Find(lhs->lhs->text);
  if (block == nullptr) return nullptr;
  std::string_view member = lhs->text;
  if (lhs->rhs != nullptr && lhs->rhs->kind == ExprKind::kIdentifier) {
    member = lhs->rhs->text;
  }
  if (member.empty()) return nullptr;
  for (const auto& sig : block->signals) {
    if (sig.signal_name != member) continue;
    // §14.3: "clocking block outputs (output or inout) are used to drive
    // values onto their corresponding signals". An input clockvar names a
    // sampled value and is not a drive target, so it is left to decline here
    // rather than driven.
    if (sig.direction == ClockingDir::kInput) return nullptr;
    *block_name = lhs->lhs->text;
    return &sig;
  }
  return nullptr;
}

// §14.16: "Clocking block outputs (output or inout) are used to drive values
// onto their corresponding signals, but at a specified time. In other words,
// the corresponding signal changes value at the indicated clocking event as
// modified by the output skew." A synchronous drive is written with the
// nonblocking operator and reaches this function as one, so the clockvar target
// is recognised here and handed to ClockingManager::ScheduleOutputDrive, which
// places the value in the Re-NBA region the clause names. Returns whether the
// left-hand side was a clockvar; a false answer leaves the ordinary
// nonblocking paths to it.
//
// The drive carries the whole value the right-hand side produced. §14.16 also
// admits a bit-select and a slice of a clockvar -- `dom.sig[2]`, `dom.sig[8:2]`
// -- and those reach here as a select of a member access rather than as a
// member access, so they are not clockvars to this function and take the
// ordinary path, which finds no variable for them and drops them. That is the
// state they were already in.
static bool TryScheduleClockvarDrive(const Expr* lhs, const Logic4Vec& rhs_val,
                                     SimContext& ctx) {
  std::string_view block_name;
  const ClockingSignal* sig = FindClockvarSignal(lhs, ctx, &block_name);
  if (sig == nullptr) return false;
  ctx.GetClockingManager()->ScheduleOutputDrive(block_name, sig->signal_name,
                                                rhs_val.ToUint64(), ctx,
                                                ctx.GetScheduler());
  return true;
}

static void ScheduleFieldNba(const Expr* lhs, const Logic4Vec& rhs_val,
                             uint64_t delay_ticks, SimContext& ctx,
                             Arena& arena) {
  // A member access is the production this answers for, and it is the one the
  // blocking form gates the same fallback on (AssignToScalarLhs and
  // PerformBlockingAssign both ask WriteStructField on that kind alone), so the
  // two forms reach it on the same left-hand sides and no others.
  if (lhs->kind != ExprKind::kMemberAccess) return;
  FieldTarget target = ResolveFieldTarget(lhs, ctx);
  if (!target.HasDeposit()) return;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->kind = EventKind::kUpdate;
  event->callback = [target, rhs_val, &ctx, &arena]() {
    WriteResolvedField(target, rhs_val, ctx, arena);
  };
  ScheduleNbaEvent(event, delay_ticks, ctx);
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
  bool absent_element = false;
  auto* elem = ResolveNbaSelectElement(stmt->lhs, ctx, arena, &absent_element);
  // §7.4.5, as on the blocking path: a write to an array with an invalid index
  // performs no operation, and the fallback below would otherwise take the
  // name down to the array's base carrier.
  if (absent_element) return;
  // §11.5.1's bit of an unpacked element: the object the trailing index selects
  // within, which is not an element and so must not be written whole. It stands
  // in for ResolveLhsVariable, which would answer the array's base carrier and
  // let the window below be resolved against that.
  auto* sub_elem =
      elem ? nullptr : TryResolveCompoundElementBase(stmt->lhs, ctx, arena);
  auto* var = elem                  ? elem
              : sub_elem != nullptr ? sub_elem
                                    : ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) {
    // §14.16: a clockvar target is a synchronous drive rather than a member of
    // an object, and it is asked before the field path because the field path
    // resolves `cb` as a variable and finds none.
    if (TryScheduleClockvarDrive(stmt->lhs, rhs_val, ctx)) return;
    ScheduleFieldNba(stmt->lhs, rhs_val, delay_ticks, ctx, arena);
    return;
  }

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
  ScheduleNbaEvent(event, delay_ticks, ctx);
}

}  // namespace delta
