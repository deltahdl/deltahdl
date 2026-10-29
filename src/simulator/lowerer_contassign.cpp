// §10.3: lowering a continuous assignment into the process that drives its
// target, and everything that process needs to decide what to drive and when.
//
// A continuous assignment puts a value onto a net, and
// what makes it a group of its own is that the value alone does not settle the
// question. §10.3.3's delay control decides when the value lands and which of
// the rise, fall and turn-off delays applies; §28.11's strengths decide what a
// net resolves to when more than one driver reaches it; and §10.3 admits a
// variable as a target as well as a net, which is written by a different route
// from either.
//
// These stood in src/simulator/lowerer.cpp, which reached 992 lines against the
// 1000 assert-no-oversized-source-files in .github/workflows/deltahdl.yml fails
// at. Nothing here is called from that file and nothing here calls into it but
// ScheduleProcess, which src/simulator/lowerer.h declares because §9.2's
// procedures and §10.3's assignments are started the same way.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "simulator/awaiters.h"
#include "simulator/contassign_delay.h"
#include "simulator/contassign_strength.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/interconnect_drive.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_contassign_driver.h"
#include "simulator/module_path_delay.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

namespace delta {

static bool Logic4VecEqual(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return false;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return false;
  }
  return true;
}

struct ContAssignDelayExprs {
  const Expr* rise = nullptr;
  const Expr* fall = nullptr;
  const Expr* decay = nullptr;
};

struct ContAssignParams {
  const Expr* lhs;
  const Expr* rhs;
  DriverStrength ds;
  ContAssignDelayExprs delays;
  uint32_t width = 0;
  // §10.3.3: the assignment to a concatenation this one is an element of,
  // whose transition picks the delay (SelectTransitionDelay).
  ContAssignWhole whole;

  // The hierarchical prefix of the module instance this assignment was lowered
  // in, ending in a `.` and empty at the top. It is Lowerer::inst_prefix_ as it
  // stood, and it is here because §30.4's module path names its destination by
  // the bare port name of the module declaring it: two instances of one cell
  // declare a path to the same `y`, and the prefix is what says which `y` this
  // assignment drives.
  std::string inst_prefix;

  // §32.4.4: the SDF names of this assignment's interconnect load and source,
  // empty for every assignment that is not a §23.3.2 input port connection.
  // RtlirContAssign::interconnect_load says how they are spelled and why.
  std::string interconnect_load;
  std::string interconnect_source;

  bool nonresistive_switch = false;

  bool resistive_switch = false;
  const Expr* data_input = nullptr;

  // §28.6: the control and the transmitted value of a three-state gate, null
  // for every other assignment. Table 28-5 answers by them: a control of x or z
  // gives the gate an output of L or H, which is a range on one side of the
  // strength scale rather than a value, and which side it is comes from the
  // value the gate would transmit.
  const Expr* three_state_ctrl = nullptr;
  const Expr* three_state_pass = nullptr;

  // The driver slot PresetDelayedDriver gave this assignment on its net when it
  // was lowered, or -1 where it gave none.
  int64_t preset_driver = -1;

  // §30.4.1 with §30.6: RtlirContAssign::module_path_port, the output port
  // whose module path delays this connection carries; and, for an assignment
  // inside the instance, whether the connection of the port it drives carries
  // them instead, so it does not delay the port a second time.
  std::string module_path_port;
  bool path_delayed_at_connection = false;
};

static ContAssignDelays BuildContAssignDelays(const ContAssignDelayExprs& exprs,
                                              SimContext& ctx, Arena& arena) {
  ContAssignDelays d;
  // §22.7: each delay, the charge decay time among them, counts the time unit
  // of the module declaring it, and the ticks it waits are the design's.
  d.rise = DelayExprToTicks(exprs.rise, ctx, arena);
  d.fall = exprs.fall ? DelayExprToTicks(exprs.fall, ctx, arena) : 0;
  d.decay = exprs.decay ? DelayExprToTicks(exprs.decay, ctx, arena) : 0;
  d.has_fall = exprs.fall != nullptr;
  d.has_decay = exprs.decay != nullptr;
  return d;
}

// The two bits one scalar value carries, as §28.6's tables name them: 0, 1, x
// or z of the least significant bit.
enum class GateBit : uint8_t { kZero, kOne, kUnknown, kHighz };

static GateBit LowGateBit(const Logic4Vec& v) {
  if (v.nwords == 0) return GateBit::kUnknown;
  bool aval = (v.words[0].aval & 1) != 0;
  bool bval = (v.words[0].bval & 1) != 0;
  if (!bval) return aval ? GateBit::kOne : GateBit::kZero;
  return aval ? GateBit::kUnknown : GateBit::kHighz;
}

// §28.6 Table 28-5: a three-state gate whose control is x or z drives L or H --
// L standing for an outcome that is 0 or z and H for one that is 1 or z --
// where an unknown control
// with an unknown or high-impedance data value drives a plain x. §28.12.2 draws
// L and H as a range on one side of the strength scale, from the gate's own
// drive level down to high impedance (Figure 28-6 through Figure 28-8), and a
// driver spells that by putting the other side of its strength at the
// high-impedance level: the value the gate's own conditional yields is x for
// all three cases, and the strength is what tells them apart.
//
// A control of 0 or 1 leaves the gate driving what Table 28-5's first two
// columns give at the strength it drives with, which is `drive`: the strength
// its declaration named, or for a MOS switch the strength of what it passes
// (§28.13), which Table 28-6's L and H then put on one side of the scale.
static DriverStrength ThreeStateGateStrength(const ContAssignParams& params,
                                             DriverStrength drive,
                                             SimContext& ctx, Arena& arena) {
  GateBit ctrl = LowGateBit(EvalExpr(params.three_state_ctrl, ctx, arena));
  if (ctrl == GateBit::kZero || ctrl == GateBit::kOne) return drive;
  GateBit passed = LowGateBit(EvalExpr(params.three_state_pass, ctx, arena));
  DriverStrength one_sided = drive;
  if (passed == GateBit::kZero) {
    one_sided.s1 = Strength::kHighz;
    return one_sided;
  }
  if (passed == GateBit::kOne) {
    one_sided.s0 = Strength::kHighz;
    return one_sided;
  }
  return drive;
}

// The net a MOS or CMOS switch's data input reads: the one it names, by its
// simple or its hierarchical name, or the one a bit-select of it selects from.
// Null for anything else, a variable or a constant.
static Net* DataInputNet(const Expr* data, SimContext& ctx) {
  const Expr* base = data->kind == ExprKind::kSelect ? data->base : data;
  if (base->kind == ExprKind::kMemberAccess) {
    return FindHierarchicalNet(base, ctx);
  }
  return base->kind == ExprKind::kIdentifier ? ctx.FindNet(base->text)
                                             : nullptr;
}

// §28.13 and §28.14: the strength a MOS or CMOS switch's data input carries
// into it: a net's, the one bit's of a net a bit-select names, and strong for
// anything else, a variable or a constant driving at strong. A select past
// the declared range is answered with the net's whole strength by
// Net::BitStrength, the value it reads being x.
static NetStrength DataInputStrength(const Expr* data, SimContext& ctx) {
  Net* net = DataInputNet(data, ctx);
  if (net == nullptr) {
    return {Strength::kStrong, Strength::kStrong, Strength::kStrong,
            Strength::kStrong};
  }
  if (data->kind != ExprKind::kSelect) return net->resolved_strength;
  int64_t index = SelectBoundValue(EvalExpr(data->index, ctx, ctx.GetArena()));
  PackedRange range = net->resolved->DeclaredRange();
  return net->BitStrength(static_cast<uint32_t>(range.OffsetOf(index)));
}

// The lower end of a range a switch passes, reduced as its upper end is, or
// high impedance where the reduced range is one level (DriverStrength::s0_lo).
static Strength ReducedRangeLow(Strength (*reduce)(Strength), Strength hi,
                                Strength lo) {
  Strength low = reduce(lo);
  return low == reduce(hi) ? Strength::kHighz : low;
}

static DriverStrength ComputeEffectiveDriverStrength(
    const ContAssignParams& params, SimContext& ctx) {
  DriverStrength effective_ds = params.ds;
  if (params.nonresistive_switch || params.resistive_switch) {
    NetStrength ns = DataInputStrength(params.data_input, ctx);
    auto reduce =
        params.resistive_switch ? &ReduceResistive : &ReduceNonresistive;
    effective_ds = {reduce(ns.s0_hi), reduce(ns.s1_hi),
                    ReducedRangeLow(reduce, ns.s0_hi, ns.s0_lo),
                    ReducedRangeLow(reduce, ns.s1_hi, ns.s1_lo)};
  }
  if (params.three_state_ctrl != nullptr &&
      params.three_state_pass != nullptr) {
    return ThreeStateGateStrength(params, effective_ds, ctx, ctx.GetArena());
  }
  return effective_ds;
}

// The value a continuous assignment drives, at the target's width, a stream
// left-aligned in it or reported narrower as §11.4.14 has a procedural
// assignment's (WidenStreamPackToFixedTarget).
static Logic4Vec EvalContAssignRhs(const ContAssignParams& params,
                                   SimContext& ctx, Arena& arena) {
  Logic4Vec value = EvalExpr(params.rhs, ctx, arena, params.width);
  if (params.rhs->kind != ExprKind::kStreamingConcat || params.width == 0)
    return value;
  return WidenStreamPackToFixedTarget(value, params.width,
                                      params.rhs->range.start, ctx, arena);
}

// True for the left-hand-side forms a continuous assignment can drive beyond a
// bare identifier: a part-select/element select, a concatenation, an assignment
// pattern, a streaming concatenation, or a member access. These reuse the
// procedural lvalue writer (PerformBlockingAssign) below.
static bool ContAssignSupportsStructuredLhs(ExprKind k) {
  return k == ExprKind::kSelect || k == ExprKind::kConcatenation ||
         k == ExprKind::kAssignmentPattern || k == ExprKind::kStreamingConcat ||
         k == ExprKind::kMemberAccess;
}

static void ApplyContAssignToVariable(const ContAssignParams& params,
                                      const Logic4Vec& driven_val,
                                      SimContext& ctx, Arena& arena) {
  if (params.lhs->kind != ExprKind::kIdentifier) {
    // A concatenation, part-select, member, or streaming-concat target reuses
    // the procedural lvalue writer, which decomposes the lvalue and notifies
    // each affected variable's watchers (§11.4.1; §23.3.3.5 output
    // distribution drives instance outputs into part-selects of a parent net).
    PerformBlockingAssign(params.lhs, driven_val, ctx, arena);
    return;
  }
  // §10.10 with §10.8 (printed pages 264 and 259): braces a continuous
  // assignment drives into a fixed-size unpacked array are an unpacked array
  // concatenation, each item an element, laid into the array's elements as a
  // procedural assignment lays them, each time an operand changes.
  if (params.rhs->kind == ExprKind::kConcatenation) {
    if (const ArrayInfo* info = ctx.FindArrayInfo(params.lhs->text)) {
      DistributeConcatToArray(params.lhs->text, *info, params.rhs, ctx, arena);
      return;
    }
  }
  auto* var = ctx.FindVariable(params.lhs->text);
  if (var == nullptr) return;
  // §10.6.2: a release of the variable reestablishes this assignment and
  // schedules its reevaluation, which ReleaseForcedTarget reaches through
  // this. Recorded on the first drive, whether or not the variable is held
  // then, and from what outlives the coroutine.
  if (!var->cont_assign_reevaluate) {
    var->cont_assign_reevaluate = [params, &ctx, &arena]() {
      ApplyContAssignToVariable(params, EvalContAssignRhs(params, ctx, arena),
                                ctx, arena);
    };
  }
  // §6.5 (printed page 91): the value converts to the variable's type as an
  // assignment's does -- a real by §6.12.1, a 2-state variable taking 0 for an
  // x or a z -- and the strength it was driven with is lost.
  WriteVar(var, ConvertRealOnAssign(driven_val, params.lhs, *var, ctx, arena),
           arena);
}

static void ApplyContAssignResult(const ContAssignParams& params,
                                  const ContAssignDriver& drv,
                                  const ContAssignDrivenValue& driven,
                                  SimContext& ctx, Arena& arena) {
  if (drv.net) {
    ApplyContAssignToNet(drv, driven, &ctx.GetScheduler(), arena);
  } else {
    ApplyContAssignToVariable(params, driven.value, ctx, arena);
  }
}

// The value a transition is read from, which §10.3.3's rules read to choose
// among an assignment's rise, fall and turn-off delays. For a select the target
// is the selected bits, so the comparison is against those bits and not
// against the whole net around them.
//
// §28.16's Table 28-9 reads a gate's transition from the value its output had,
// and §10.3.3 handles an assignment's delay as a gate's: once the assignment
// has driven a net, the transition is from what it drove last, which is its
// own slot among the net's drivers. The net's value is what every source of it
// resolves to, so on a net others drive too it is no value of this one's: a
// buf falling from 1 to 0 on a wand another driver holds at 0 compared 0 with
// 0 and took the rise delay.
static Logic4Vec CurrentContAssignOldValue(const ContAssignParams& params,
                                           const ContAssignDriver& drv,
                                           SimContext& ctx, Arena& arena) {
  if (drv.net != nullptr && !drv.first) {
    const Logic4Vec& own = drv.net->drivers[drv.driver_idx];
    return drv.partial ? ExtractBitField(arena, own, drv.lo, drv.width) : own;
  }
  Logic4Vec old_val = MakeLogic4VecVal(arena, 1, 0);
  auto* var = params.lhs->kind == ExprKind::kIdentifier
                  ? ctx.FindVariable(params.lhs->text)
                  : nullptr;
  if (var) {
    old_val = var->value;
  } else if (drv.net && drv.net->resolved) {
    old_val = drv.partial ? ExtractBitField(arena, drv.net->resolved->value,
                                            drv.lo, drv.width)
                          : drv.net->resolved->value;
  }
  return old_val;
}

// The bits of the right-hand value this driver lands, which is what §10.3.3's
// transition reads against the target's present value.
// CurrentContAssignOldValue above already answers with the selected bits alone,
// and until this stood beside it the two sides of that comparison were not the
// same bits and not even the same width: the whole value as written was
// compared against the window it lands in.
//
// §11.5.1 says which of the value's bits those are. A write through a partially
// out-of-range part-select changes only the bits that are in range, and the
// bits it affects take the value's bits at and above `src_lo` rather
// than its least significant ones -- the same projection ContAssignDriverValue
// makes before depositing them. On a `tri0 [7:0] a`, `a[1 -: 4]` is `a[1:-2]`,
// so `assign #(2,3) a[1 -: 4] = 4'b0011` lands 2'b00 on a[1:0]: a transition to
// zero, which §10.3.3 gives its second delay, the fall delay, where the whole
// 4'b0011 is nonzero and took the rise.
//
// The commit path keeps the value as written. ContAssignDriverValue makes this
// projection for itself, and ApplyHighzStrengthsToValue before it reads the
// select's own width.
static Logic4Vec ContAssignDrivenBits(const ContAssignDriver& drv,
                                      const Logic4Vec& val, Arena& arena) {
  if (!drv.partial || drv.width == 0) return val;
  return ExtractBitField(arena,
                         ResizeToWidth(val, drv.src_lo + drv.width, arena),
                         drv.src_lo, drv.width);
}

// How wide the transition §10.3.3 is choosing a delay for is: the bits driven,
// which for a select partly out of range are fewer than the select declares.
// The width decides which of the clause's two tables applies -- one bit takes
// the scalar transition table -- so a one-bit window inside a wider select took
// the vector arm and answered the rise delay where the scalar table gives a
// z-to-0 transition the fall.
static uint32_t ContAssignTransitionWidth(const ContAssignDriver& drv,
                                          uint32_t declared_width) {
  return drv.partial ? drv.width : declared_width;
}

// Tracks the result of re-evaluating the right-hand side after an inertial
// delay is interrupted by an operand change. `collapsed` requests that the
// pending transition be dropped because the new value already equals the
// left-hand side. `rescheduled` is true only when the operand changed and a new
// fire time was computed into `target`; otherwise the caller keeps its existing
// target unchanged.
struct InertialReeval {
  bool collapsed = false;
  bool rescheduled = false;
  SimTime target;
};

// The endpoints of a pending inertial continuous-assignment transition (IEEE
// 1800 §28 inertial delays): `old_val` is the value already present on the
// left-hand side and `val` is the pending new value being scheduled. `val` is a
// reference because re-evaluating the right-hand side may replace it in place.
struct PendingContAssignTransition {
  const Logic4Vec& old_val;
  Logic4Vec& val;
};

// The loop-invariant context threaded through the inertial-delay re-evaluation
// of a continuous assignment (IEEE 1800 §28 inertial delays): the assignment
// parameters, the resolved delay set, and the simulation context/arena used to
// re-evaluate the right-hand side. Bundled so the per-iteration helper stays
// within a small parameter count.
struct InertialLoopCtx {
  const ContAssignParams& params;
  const ContAssignDelays& d;
  // Which bits of the target this assignment drives, since the delay a
  // re-evaluation chooses is a delay for that transition rather than for the
  // whole value.
  const ContAssignDriver& drv;
  SimContext& ctx;
  Arena& arena;
};

static InertialReeval ReevalInertialContAssign(
    const InertialLoopCtx& loop, const PendingContAssignTransition& xition) {
  InertialReeval result;
  auto new_val = EvalContAssignRhs(loop.params, loop.ctx, loop.arena);
  if (Logic4VecEqual(new_val, xition.val)) return result;
  // The operand changed again before the pending value could propagate, so the
  // previously scheduled event is dropped.
  xition.val = new_val;
  // The comparison and the delay are about the bits that land, which is what
  // `old_val` already holds: a re-evaluation reaches the same §10.3.3 question
  // the first evaluation did, and has to read the same two operands.
  auto driven = ContAssignDrivenBits(loop.drv, new_val, loop.arena);
  if (Logic4VecEqual(driven, xition.old_val)) {
    // The re-evaluated right-hand side now matches the value already present on
    // the left-hand side, so no replacement event is scheduled and the pending
    // transition collapses immediately.
    result.collapsed = true;
    return result;
  }
  uint64_t ticks = SelectTransitionDelay(
      loop.params.whole,
      {xition.old_val, driven,
       ContAssignTransitionWidth(loop.drv, loop.params.width)},
      loop.d, loop.ctx, loop.arena);
  result.rescheduled = true;
  result.target = loop.ctx.CurrentTime() + SimTime{ticks};
  return result;
}

static void CommitContAssignValue(const ContAssignParams& params,
                                  const ContAssignDriver& drv,
                                  const Logic4Vec& val, SimContext& ctx,
                                  Arena& arena) {
  DriverStrength effective_ds = ComputeEffectiveDriverStrength(params, ctx);
  auto driven_val = ApplyHighzStrengthsToValue(val, effective_ds, arena);
  ApplyContAssignResult(
      params, drv, ContAssignDrivenValue{driven_val, effective_ds}, ctx, arena);
}

// §10.3.2: the net this assignment drives, or a driver with no net where the
// target is a variable or an lvalue this does not decompose. Which bits of the
// net a select names is left to RefreshContAssignDriverBits below, which reads
// it again before each evaluation drives them. A concatenation, a streaming
// concatenation and a member access each reach something other than one run of
// one net's bits -- Example 2 of §10.3.2 writes `assign {carry_out, sum_out} =
// ...`, which is two nets -- so they keep the direct write
// ApplyContAssignToVariable does and are not drivers yet. A member access that
// names a net is the exception: `b.y` of an interface instance, or `p.y`
// through an interface port aliased to it (§25.3.2), is that one net (§23.6),
// and written directly it took the value with no strength and no combining
// with the net's other drivers, where §28.12.1 (printed page 844) has the
// stronger of two signals win.
static Net* NetNamedBy(const Expr* e, SimContext& ctx) {
  if (e->kind == ExprKind::kIdentifier) return ctx.FindNet(e->text);
  if (e->kind != ExprKind::kMemberAccess) return nullptr;
  return FindHierarchicalNet(e, ctx);
}

// §7.4.2 (printed page 154): an element of a net array is used as a scalar or
// vector net would be, so `assign n[1] = ...` on `wire n[0:2]`
// drives the element n[1] as a whole, the net held under "n[1]"
// (CreateDeclaredNet in lowerer_register.cpp). The index of a net_lvalue is a
// constant_select (A.8.5), so the element is fixed at lowering. Null for a
// select of anything but a net array, and for an index naming no element.
static Net* NetArrayElementNamedBy(const Expr* e, SimContext& ctx) {
  if (e->kind != ExprKind::kSelect || e->index_end != nullptr ||
      e->base == nullptr || e->base->kind != ExprKind::kIdentifier ||
      e->index == nullptr) {
    return nullptr;
  }
  std::string_view name = e->base->text;
  if (ctx.FindArrayInfo(name) == nullptr || ctx.FindNet(name) == nullptr) {
    return nullptr;
  }
  Logic4Vec idx = EvalExpr(e->index, ctx, ctx.GetArena());
  if (!idx.IsKnown()) return nullptr;
  return ctx.FindNet(std::string(name) + "[" + std::to_string(idx.ToUint64()) +
                     "]");
}

static ContAssignDriver MakeContAssignDriver(const Expr* lhs, SimContext& ctx) {
  ContAssignDriver drv;
  if (lhs->kind == ExprKind::kIdentifier ||
      lhs->kind == ExprKind::kMemberAccess) {
    drv.net = NetNamedBy(lhs, ctx);
  } else if (Net* elem = NetArrayElementNamedBy(lhs, ctx)) {
    drv.net = elem;
  } else if (lhs->kind == ExprKind::kSelect && lhs->base != nullptr) {
    Net* net = NetNamedBy(lhs->base, ctx);
    if (net == nullptr) net = NetArrayElementNamedBy(lhs->base, ctx);
    if (net != nullptr && net->resolved != nullptr) {
      drv.net = net;
      drv.partial = true;
    }
  }
  drv.driver_idx = drv.net ? drv.net->drivers.size() : 0;
  drv.first = true;
  // §21.7.4.3.2: the instance the assignment stands in.
  if (const Process* proc = ctx.CurrentProcess())
    drv.origin = proc->inst_prefix;
  return drv;
}

// Re-reads which bits of the net a select target names, before each evaluation
// drives them. §10.3.2 makes a continuous assignment continuous and automatic,
// so an index that is itself an operand moves the driven bits when it changes,
// the way it moves the bits a procedural write reaches. The driver slot does
// not move with them: it is the same assignment driving the same net,
// contributing high impedance wherever its index is not currently pointing.
static void RefreshContAssignDriverBits(ContAssignDriver& drv, const Expr* lhs,
                                        SimContext& ctx, Arena& arena) {
  if (!drv.partial || drv.net == nullptr) return;
  PartSelectBits bits = SelectStorageBits(*drv.net->resolved, lhs, ctx, arena);
  drv.lo = bits.lo;
  drv.width = bits.width;
  drv.src_lo = bits.src_lo;
}

static uint64_t RemainingTicks(SimTime target, SimContext& ctx) {
  return (target.ticks > ctx.CurrentTime().ticks)
             ? (target.ticks - ctx.CurrentTime().ticks)
             : 0;
}

// Re-evaluates the right-hand side after an inertial delay was interrupted and
// decides how the pending transition continues. Returns true when the loop
// should stop (the pending value collapsed onto the left-hand side); otherwise
// returns false and updates `target` if the operand change rescheduled the
// fire time.
static bool ApplyInertialReeval(const InertialLoopCtx& loop,
                                const PendingContAssignTransition& xition,
                                SimTime& target) {
  InertialReeval re = ReevalInertialContAssign(loop, xition);
  if (re.collapsed) return true;
  if (re.rescheduled) target = re.target;
  return false;
}

// Runs the inertial-delay wait loop for one pending continuous-assignment
// transition (IEEE 1800 §28 inertial delays). Each iteration waits out the
// remaining ticks; an operand change during the wait re-evaluates the
// right-hand side, which either collapses the pending value onto the
// left-hand side (loop stops) or reschedules the fire time. Factored into its
// own awaitable coroutine so the driver coroutine stays flat; the two awaiters
// run exactly as they would inline because they reference the shared context.
static ExecTask RunInertialContAssignDelay(
    const InertialLoopCtx& loop, const std::vector<std::string_view>& read_vars,
    const Logic4Vec& old_val, Logic4Vec& val, uint64_t ticks) {
  SimTime target = loop.ctx.CurrentTime() + SimTime{ticks};
  for (uint64_t remaining = RemainingTicks(target, loop.ctx); remaining > 0;
       remaining = RemainingTicks(target, loop.ctx)) {
    if (co_await InertialDelayAwaiter{loop.ctx, remaining, read_vars}) break;
    if (ApplyInertialReeval(loop, PendingContAssignTransition{old_val, val},
                            target))
      break;
  }
  co_return StmtResult::kDone;
}

// §30.4: the net this assignment drives, which is the signal a module path can
// name as its destination. §30.4.1 makes that destination a net or variable
// wired to an output or inout port of the module, and §10.3.2 lets
// the driver of such a net name a select of it, so the destination is the same
// net whichever way the left-hand side is written: the identifier of a bare
// target, and the base of a select. That is the name MakeContAssignDriver above
// already resolves the driver against.
static std::string_view ContAssignTargetName(const Expr* lhs) {
  if (lhs == nullptr) return {};
  if (lhs->kind == ExprKind::kIdentifier) return lhs->text;
  if (lhs->kind == ExprKind::kSelect && lhs->base != nullptr &&
      lhs->base->kind == ExprKind::kIdentifier) {
    return lhs->base->text;
  }
  return {};
}

// The manager to consult for a module path delay onto `target`, or null when no
// registered module path names it as a destination. Null is the answer for
// every target in a design that declared no specify block, and for a left-hand
// side that names no net at all, which no module path can be written against.
static const SpecifyManager* ModulePathManagerFor(SimContext& ctx,
                                                  std::string_view target) {
  if (target.empty()) return nullptr;
  const SpecifyManager* mgr = ctx.GetSpecifyManager();
  if (mgr == nullptr) return nullptr;
  if (!IsModulePathOutput(*mgr, target)) return nullptr;
  return mgr;
}

// Everything the wait before a continuous assignment's commit needs. The wait
// has two forms: §28's inertial delay, taken from the assignment's own delay
// expressions, and §30.4's module path delay, which a specify block declares
// onto whatever drives the path output. `path_mgr` is null unless a registered
// module path names this assignment's target, and `commit` is how either form
// drives it.
struct ContAssignWait {
  const ContAssignParams& params;
  SimContext& ctx;
  Arena& arena;
  const std::vector<std::string_view>& read_vars;
  const SpecifyManager* path_mgr;
  std::string_view path_output;
  const std::function<void(const Logic4Vec&)>& commit;
};

// §32.4.1 Table 32-1 (printed page 925): a DEVICE entry on a cell with no
// specify paths annotates the primitives driving its outputs, so a gate lowered
// to this assignment takes the rise, fall and turn-off delays the entry gave
// its driver in place of its own. Read on every transition, as an interconnect
// delay is, since $sdf_annotate runs during simulation. Kept on the driver
// alone, the annotation timed nothing: the gate went on waiting out its #1.
// False, leaving `d` alone, where no DEVICE entry reached the driver.
static bool AnnotatedGateDelays(const ContAssignParams& params, SimContext& ctx,
                                ContAssignDelays& d) {
  const SpecifyManager* mgr = ctx.GetSpecifyManager();
  if (mgr == nullptr) return false;
  const PrimitiveDriver* driver = mgr->FindAnnotatedPrimitiveDriver(
      params.inst_prefix, ContAssignTargetName(params.lhs));
  if (driver == nullptr) return false;
  d.rise = driver->delays[0];
  d.fall = driver->delays[1];
  d.decay = driver->delays[2];
  d.has_fall = true;
  d.has_decay = true;
  return true;
}

// Waits out one pending transition, reporting through `*committed` whether the
// wait already drove the target. Only the module path route ever does, because
// §30.7's pulse filtering places two values on the output -- x and then the
// value the pulse returned to, or the pulse's own two edges. Every other wait
// leaves the single commit to the caller.
static ExecTask RunContAssignWait(const ContAssignWait& w,
                                  const ContAssignDriver& drv, Logic4Vec& val,
                                  bool* committed) {
  ContAssignDelays d;
  bool delayed = w.params.delays.rise != nullptr;
  if (delayed) d = BuildContAssignDelays(w.params.delays, w.ctx, w.arena);
  if (AnnotatedGateDelays(w.params, w.ctx, d)) delayed = true;
  Logic4Vec old_val = CurrentContAssignOldValue(w.params, drv, w.ctx, w.arena);
  Logic4Vec driven = ContAssignDrivenBits(drv, val, w.arena);
  uint64_t ticks = delayed
                       ? SelectTransitionDelay(
                             w.params.whole,
                             {old_val, driven,
                              ContAssignTransitionWidth(drv, w.params.width)},
                             d, w.ctx, w.arena)
                       : 0;

  // An output port's connection places its first value on the net above at
  // once and delays later ones; where a path leads to the port that value is x,
  // not the undriven z of §23.3.3.3 (§28.16, printed page 856, with §30.4).
  const bool kFirstAtPort = !w.params.module_path_port.empty() && drv.first;
  if (kFirstAtPort && w.path_mgr != nullptr &&
      !ModulePathSourcesOf(*w.path_mgr, w.path_output).empty()) {
    val = MakeAllX(w.arena, val.width);
  }
  if (w.path_mgr != nullptr && !kFirstAtPort &&
      !Logic4VecEqual(driven, old_val)) {
    // At the port the wait also wakes on the paths' sources, whose moves in
    // the scheduling step reselect the delay (RunModulePathTransition).
    const bool kAtPort = !w.params.module_path_port.empty();
    std::vector<std::string> path_sources;
    std::vector<std::string_view> wake = w.read_vars;
    if (kAtPort) {
      path_sources = ModulePathSourcesOf(*w.path_mgr, w.path_output);
      wake.insert(wake.end(), path_sources.begin(), path_sources.end());
    }
    ModulePathDrive drive{w.ctx,    w.arena,      *w.path_mgr,    w.path_output,
                          wake,     w.params.rhs, w.params.width, ticks,
                          w.commit, kAtPort};
    co_await RunModulePathTransition(drive, old_val, val, committed);
    co_return StmtResult::kDone;
  }

  if (ticks > 0 && !w.read_vars.empty()) {
    InertialLoopCtx loop{w.params, d, drv, w.ctx, w.arena};
    co_await RunInertialContAssignDelay(loop, w.read_vars, old_val, val, ticks);
  } else if (ticks > 0) {
    co_await DelayAwaiter{w.ctx, ticks};
  }
  co_return StmtResult::kDone;
}

// Everything the §32.4.4 lookup below reads. Bundled because the question it
// answers is about one transition of one assignment, and the five things that
// take are what a §30.4 module path drive already bundles for the same reason.
struct InterconnectDelayQuery {
  const ContAssignParams& params;
  const ContAssignDriver& drv;
  const Logic4Vec& val;
  SimContext& ctx;
  Arena& arena;
};

// §32.4.4: the load sees the value only once the interconnect delay annotated
// between the connection's two names has passed, each change of the source
// carried across on its own (DriveAcrossInterconnect). An assignment with
// nothing annotated between its two names commits at once, which is what
// every continuous assignment did before.
//
// The delay is read on every evaluation rather than once when the coroutine
// starts, which is what a module path delay does: §32.9's $sdf_annotate is a
// system task executed during simulation, so the annotation may not exist yet
// the first time this assignment runs and may be replaced by a later call.
static void CommitAcrossInterconnect(
    const InterconnectDelayQuery& q,
    const std::shared_ptr<InterconnectSchedule>& schedule,
    const std::function<void(const Logic4Vec&)>& commit) {
  const SpecifyManager* mgr = q.ctx.GetSpecifyManager();
  // §32.4.4: a load with a delay of its own from some source of the net it
  // reads takes each source's changes across that source's delay, which the
  // net's drivers carry to it (FollowNetDrivers), not the net's one value.
  if (schedule->shadow != nullptr && mgr != nullptr &&
      mgr->HasSourceSpecificInterconnectDelay(q.params.interconnect_load)) {
    return;
  }
  const std::optional<InterconnectDelay> kAnnotated =
      q.params.interconnect_load.empty() || mgr == nullptr
          ? std::nullopt
          : mgr->ConnectionInterconnectDelay(q.params.interconnect_source,
                                             q.params.interconnect_load);
  if (!kAnnotated.has_value() && schedule->pending.empty()) {
    commit(q.val);
    return;
  }
  const Logic4Vec kHeld =
      CurrentContAssignOldValue(q.params, q.drv, q.ctx, q.arena);
  const Logic4Vec kBits = ContAssignDrivenBits(q.drv, q.val, q.arena);
  DriveAcrossInterconnect(schedule, kAnnotated.value_or(InterconnectDelay{}),
                          InterconnectChange{kHeld, q.val, kBits}, q.ctx,
                          commit);
}

// §32.4.4: where an input port connection reads a net, the load follows each
// of the net's drivers, so that a delay annotated from one of the net's
// sources to it reaches it from that source alone.
static void FollowConnectedNet(
    const ContAssignParams& params, InterconnectSchedule& schedule,
    SimContext& ctx, const std::function<void(const Logic4Vec&)>& commit) {
  if (params.interconnect_source.empty()) return;
  std::string dotted = params.interconnect_source;
  std::ranges::replace(dotted, '/', '.');
  Net* net = ctx.FindNet(dotted);
  if (net == nullptr) return;
  schedule.shadow = std::make_shared<InterconnectShadow>();
  FollowNetDrivers(
      *net, schedule.shadow,
      InterconnectEnds{params.interconnect_source, params.interconnect_load},
      ctx, commit);
}

// The name a module path declared in this instance gives this assignment's
// target: the net the driver resolves against, under the instance prefix,
// which is what PathDelay::inst_prefix and PathDelay::dst_port together spell.
// An output port's connection names the port it carries the delays of instead,
// and an assignment inside the instance whose port's connection carries them
// names nothing.
static std::string ModulePathOutputName(const ContAssignParams& params) {
  if (!params.module_path_port.empty()) return params.module_path_port;
  if (params.path_delayed_at_connection) return {};
  std::string_view target_name = ContAssignTargetName(params.lhs);
  if (target_name.empty()) return {};
  return params.inst_prefix + std::string(target_name);
}

// §28.13 and §28.14: a MOS or CMOS switch passes its data input's strength
// on, so a change of that strength alone resumes the switch as a change of a
// value it reads does (AnyChangeAwaiter::strength_changes). Marks the net the
// data input reads to record such changes, and answers whether `params` is a
// switch's.
static bool WatchDataInputStrength(const ContAssignParams& params,
                                   SimContext& ctx) {
  if (!params.nonresistive_switch && !params.resistive_switch) return false;
  Net* net = DataInputNet(params.data_input, ctx);
  if (net != nullptr) net->strength_watched = true;
  return true;
}

static SimCoroutine MakeContAssignCoroutine(ContAssignParams params,
                                            SimContext& ctx, Arena& arena) {
  if (!params.lhs) co_return;
  bool lhs_is_name = params.lhs->kind == ExprKind::kIdentifier;
  if (!lhs_is_name && !ContAssignSupportsStructuredLhs(params.lhs->kind)) {
    co_return;
  }

  // The change-watchers and SimContext key by std::string_view, so the strings
  // backing read_vars must outlive every co_await below. Keep the owning set in
  // the coroutine frame (as MakeAlwaysCombCoroutine does) rather than returning
  // views into a helper's local set that dies on return -- otherwise a delayed
  // assignment, which arms its AnyChangeAwaiter only after the delay, reads a
  // reused buffer, FindVariable misses, and the assignment stops reacting to
  // later operand changes (IEEE 1800 §28 gate/net delays).
  std::unordered_set<std::string> read_strs;
  CollectExprAndStaticReads(params.rhs, ctx, read_strs);
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());
  DropUnwatchableNames(ctx, read_vars);
  bool passes_strength = WatchDataInputStrength(params, ctx);

  ContAssignDriver drv = MakeContAssignDriver(params.lhs, ctx);
  if (params.preset_driver >= 0 && drv.net != nullptr) {
    drv.driver_idx = static_cast<size_t>(params.preset_driver);
    drv.first = false;
  }

  // Outlives the loop, since ModulePathDrive::output is a view of it.
  std::string path_output = ModulePathOutputName(params);

  std::function<void(const Logic4Vec&)> commit = [&](const Logic4Vec& v) {
    CommitContAssignValue(params, drv, v, ctx, arena);
    drv.first = false;
  };
  // §32.4.4: the transitions on their way across an interconnect delay.
  InterconnectScheduleOwner interconnect;
  FollowConnectedNet(params, *interconnect.schedule, ctx, commit);
  // §32.4.4: the output port this assignment carries out of its instance,
  // which the net it drives records beside the driver.
  drv.source_port = params.module_path_port;

  // §30.4: a module path declared in a specify block delays whatever drives the
  // path output, and §30.7's pulse limits then decide what reaches it. The
  // manager is read here rather than at lowering because Lowerer::Lower
  // registers the specify blocks after it has lowered the modules; this body
  // first runs when the scheduler resumes it, by which time they are in. A
  // driver this answers null for takes exactly the route it took before.
  const SpecifyManager* path_mgr = ModulePathManagerFor(ctx, path_output);

  // A continuous assignment must drive its left-hand side at least once when it
  // is activated, even if a simulation stop was already requested for the
  // region in which it first runs. A program's `assign` is reactive (§24.3.1),
  // so it first executes in the Reactive region alongside the program's initial
  // procedures; if such an initial completes first it sets the stop request
  // (the program block finished, §24.7) before this coroutine's first
  // evaluation. Guarding the very first evaluation behind StopRequested would
  // then drop the assignment entirely, leaving the target at its reset value.
  bool evaluated_once = false;
  while (!evaluated_once || !ctx.StopRequested()) {
    evaluated_once = true;
    auto val = EvalContAssignRhs(params, ctx, arena);
    RefreshContAssignDriverBits(drv, params.lhs, ctx, arena);

    bool committed = false;
    if (ContAssignDelays filed; params.delays.rise || path_mgr != nullptr ||
                                AnnotatedGateDelays(params, ctx, filed)) {
      ContAssignWait wait{params,   ctx,         arena, read_vars,
                          path_mgr, path_output, commit};
      co_await RunContAssignWait(wait, drv, val, &committed);
    }

    if (!committed) {
      InterconnectDelayQuery query{params, drv, val, ctx, arena};
      CommitAcrossInterconnect(query, interconnect.schedule, commit);
    }

    // §32.4.4: an assignment reading nothing changes no more, but the
    // transitions it sent across an interconnect delay still arrive.
    if (read_vars.empty()) {
      co_await AwaitInterconnectArrivals(*interconnect.schedule, ctx);
      break;
    }
    co_await AnyChangeAwaiter{ctx, read_vars, nullptr, passes_strength};
  }
}
// §6.6 (printed page 91): a net's drivers determine its value, and it is high
// impedance only where no driver is connected to it.
// A delayed assignment's driver is connected from the start but has computed
// no value until its first transition lands after the delay (§28.16, printed
// page 856; §10.3.3), so until then it drives x, at its drive strength, on the
// bits it drives. It is given that slot here, before time 0, so the net holds
// x there from the start rather than z and no change to x is seen at time 0.
// Answers the slot, or -1 where the assignment has no delay or drives no net.
static int64_t PresetDelayedDriver(const ContAssignParams& p, SimContext& ctx,
                                   Arena& arena) {
  if (p.delays.rise == nullptr) return -1;
  ContAssignDriver drv = MakeContAssignDriver(p.lhs, ctx);
  if (drv.net == nullptr || drv.net->resolved == nullptr) return -1;
  RefreshContAssignDriverBits(drv, p.lhs, ctx, arena);
  auto slot = static_cast<int64_t>(drv.net->drivers.size());
  drv.net->drivers.push_back(ContAssignDriverValue(
      drv, MakeAllX(arena, drv.net->resolved->value.width), arena));
  drv.net->driver_strengths.push_back(p.ds);
  drv.net->Resolve(arena, nullptr);
  return slot;
}

void Lowerer::LowerContAssign(const RtlirContAssign& ca, bool from_program) {
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;

  p->home_region = from_program
                       ? Scheduler::HomeRegionForReactiveBlockingAssign()
                       : Region::kActive;
  p->is_reactive = from_program;

  p->inst_prefix = inst_prefix_;
  p->gen_prefixes.assign(ca.gen_block_prefixes.begin(),
                         ca.gen_block_prefixes.end());
  InstallGenBlockConsts(ca.gen_block_consts, p);
  ContAssignParams cap;
  cap.lhs = ca.lhs;
  cap.rhs = ca.rhs;
  cap.ds = {StrengthFromParserCode(ca.drive_strength0),
            StrengthFromParserCode(ca.drive_strength1)};
  cap.nonresistive_switch = ca.from_nonresistive_switch;
  cap.resistive_switch = ca.from_resistive_switch;
  cap.data_input = ca.data_input;
  cap.three_state_ctrl = ca.three_state_ctrl;
  cap.three_state_pass = ca.three_state_pass;
  cap.delays = {ca.delay, ca.delay_fall, ca.delay_decay};
  cap.width = ca.width;
  cap.whole = WholeOfConcatElement(ca);
  cap.inst_prefix = inst_prefix_;
  cap.interconnect_load = ca.interconnect_load;
  cap.interconnect_source = ca.interconnect_source;
  cap.preset_driver = PresetDelayedDriver(cap, ctx_, arena_);
  cap.module_path_port = ca.module_path_port;
  cap.path_delayed_at_connection = path_delayed_ports_.contains(
      inst_prefix_ + std::string(ContAssignTargetName(ca.lhs)));
  p->coro = MakeContAssignCoroutine(cap, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_);
}
}  // namespace delta
