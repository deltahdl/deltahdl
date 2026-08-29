// §10.3: lowering a continuous assignment into the process that drives its
// target, and everything that process needs to decide what to drive and when.
//
// "The continuous assignment statement shall place a value onto a net", and
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
#include <cstdint>
#include <functional>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/module_path_delay.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"

namespace delta {

static Strength ParserStrToStrength(uint8_t s) {
  switch (s) {
    case 1:
      return Strength::kHighz;
    case 2:
      return Strength::kWeak;
    case 3:
      return Strength::kPull;
    case 4:
      return Strength::kStrong;
    case 5:
      return Strength::kSupply;
    default:
      return Strength::kStrong;
  }
}

static bool Logic4VecEqual(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return false;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return false;
  }
  return true;
}

static bool IsAllHighZ(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].aval != 0 || v.words[i].bval == 0) return false;
  }
  return v.nwords > 0;
}

static Logic4Vec ApplyHighzStrengthsToValue(const Logic4Vec& val,
                                            DriverStrength ds, Arena& arena) {
  bool s0_is_z = (ds.s0 == Strength::kHighz);
  bool s1_is_z = (ds.s1 == Strength::kHighz);
  if (!s0_is_z && !s1_is_z) return val;
  auto out = MakeLogic4Vec(arena, val.width);
  out.is_real = val.is_real;
  out.is_signed = val.is_signed;
  out.is_string = val.is_string;
  for (uint32_t w = 0; w < val.nwords; ++w) {
    uint64_t a = val.words[w].aval;
    uint64_t b = val.words[w].bval;
    uint64_t mask = ~uint64_t{0};
    uint32_t bits_done = w * 64;
    if (val.width > bits_done && val.width - bits_done < 64)
      mask = (uint64_t{1} << (val.width - bits_done)) - 1;
    uint64_t to_z = 0;
    if (s0_is_z) to_z |= (~a & ~b) & mask;
    if (s1_is_z) to_z |= (a & ~b) & mask;
    // A high-impedance bit is z = (aval=0, bval=1).
    out.words[w].aval = a & ~to_z;
    out.words[w].bval = b | to_z;
  }
  return out;
}

struct ContAssignDelays {
  uint64_t rise = 0;
  uint64_t fall = 0;
  uint64_t decay = 0;
  bool has_fall = false;
  bool has_decay = false;
};

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

  bool nonresistive_switch = false;

  bool resistive_switch = false;
  const Expr* data_input = nullptr;
};

// Identifies the driver slot that a continuous assignment writes to. Per IEEE
// 1800 §10.3, a continuous assignment drives a single net (or variable) through
// one driver; `net` is the resolved net (null when the target is a variable),
// `driver_idx` is that driver's slot within the net, and `first` is true on the
// initial commit, when the driver slot must be appended rather than
// overwritten.
struct ContAssignDriver {
  Net* net = nullptr;
  size_t driver_idx = 0;
  bool first = true;
};

// The value a continuous-assignment driver contributes to net resolution: the
// driven logic value paired with the driver strength selected for it (IEEE 1800
// §10.3, §28.x driver strengths).
struct ContAssignDrivenValue {
  const Logic4Vec& value;
  DriverStrength strength;
};

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

static uint64_t SelectContAssignDelay(const Logic4Vec& old_val,
                                      const Logic4Vec& new_val,
                                      const ContAssignDelays& d,
                                      uint32_t width) {
  if (!d.has_fall) return d.rise;

  bool new_is_z = IsAllHighZ(new_val);
  if (new_is_z) {
    if (d.has_decay) return d.decay;
    return std::min(d.rise, d.fall);
  }

  if (width <= 1) {
    return SelectScalarContAssignDelay(old_val, new_val, d);
  }

  if (!HasUnknownBits(new_val) && new_val.ToUint64() == 0 &&
      !HasUnknownBits(old_val) && !IsAllHighZ(old_val) &&
      old_val.ToUint64() != 0) {
    return d.fall;
  }
  return d.rise;
}

static ContAssignDelays BuildContAssignDelays(const ContAssignDelayExprs& exprs,
                                              SimContext& ctx, Arena& arena) {
  ContAssignDelays d;
  d.rise = EvalExpr(exprs.rise, ctx, arena).ToUint64();
  d.fall = exprs.fall ? EvalExpr(exprs.fall, ctx, arena).ToUint64() : 0;
  d.decay = exprs.decay ? EvalExpr(exprs.decay, ctx, arena).ToUint64() : 0;
  d.has_fall = exprs.fall != nullptr;
  d.has_decay = exprs.decay != nullptr;
  return d;
}

static DriverStrength ComputeEffectiveDriverStrength(
    const ContAssignParams& params, SimContext& ctx) {
  DriverStrength effective_ds = params.ds;
  if ((params.nonresistive_switch || params.resistive_switch) &&
      params.data_input && params.data_input->kind == ExprKind::kIdentifier) {
    auto* data_net = ctx.FindNet(params.data_input->text);
    if (data_net) {
      const NetStrength& ns = data_net->resolved_strength;
      auto reduce =
          params.resistive_switch ? &ReduceResistive : &ReduceNonresistive;
      effective_ds.s0 = reduce(ns.s0_hi);
      effective_ds.s1 = reduce(ns.s1_hi);
    }
  }
  return effective_ds;
}

static void ApplyContAssignToNet(const ContAssignDriver& drv,
                                 const ContAssignDrivenValue& driven,
                                 Scheduler* sched, Arena& arena) {
  if (drv.first) {
    drv.net->drivers.push_back(driven.value);
    drv.net->driver_strengths.push_back(driven.strength);
  } else {
    drv.net->drivers[drv.driver_idx] = driven.value;
    drv.net->driver_strengths[drv.driver_idx] = driven.strength;
  }
  // §28.16.2.1: when this update leaves a trireg net with only high-impedance
  // drivers it enters the charge storage state, and Resolve arms the charge
  // decay process by scheduling the transition to x on the scheduler. Pass the
  // scheduler through so a driver turning off actually starts that process at
  // run time (a null scheduler would silently drop it).
  drv.net->Resolve(arena, sched);
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
  auto* var = ctx.FindVariable(params.lhs->text);
  if (var && !var->is_forced) {
    var->value = ResizeToWidth(driven_val, var->value.width, arena);
    var->NotifyWatchers();
  }
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

static Logic4Vec CurrentContAssignOldValue(const ContAssignParams& params,
                                           const Net* net, SimContext& ctx,
                                           Arena& arena) {
  Logic4Vec old_val = MakeLogic4VecVal(arena, 1, 0);
  auto* var = params.lhs->kind == ExprKind::kIdentifier
                  ? ctx.FindVariable(params.lhs->text)
                  : nullptr;
  if (var)
    old_val = var->value;
  else if (net && net->resolved)
    old_val = net->resolved->value;
  return old_val;
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

static InertialReeval ReevalInertialContAssign(
    const ContAssignParams& params, const ContAssignDelays& d,
    const PendingContAssignTransition& xition, SimContext& ctx, Arena& arena) {
  InertialReeval result;
  auto new_val = EvalExpr(params.rhs, ctx, arena, params.width);
  if (Logic4VecEqual(new_val, xition.val)) return result;
  // The operand changed again before the pending value could propagate, so the
  // previously scheduled event is dropped.
  xition.val = new_val;
  if (Logic4VecEqual(new_val, xition.old_val)) {
    // The re-evaluated right-hand side now matches the value already present on
    // the left-hand side, so no replacement event is scheduled and the pending
    // transition collapses immediately.
    result.collapsed = true;
    return result;
  }
  uint64_t ticks =
      SelectContAssignDelay(xition.old_val, xition.val, d, params.width);
  result.rescheduled = true;
  result.target = ctx.CurrentTime() + SimTime{ticks};
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

static ContAssignDriver MakeContAssignDriver(Net* net) {
  ContAssignDriver drv;
  drv.net = net;
  drv.driver_idx = net ? net->drivers.size() : 0;
  drv.first = true;
  return drv;
}

// The loop-invariant context threaded through the inertial-delay re-evaluation
// of a continuous assignment (IEEE 1800 §28 inertial delays): the assignment
// parameters, the resolved delay set, and the simulation context/arena used to
// re-evaluate the right-hand side. Bundled so the per-iteration helper stays
// within a small parameter count.
struct InertialLoopCtx {
  const ContAssignParams& params;
  const ContAssignDelays& d;
  SimContext& ctx;
  Arena& arena;
};

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
  InertialReeval re = ReevalInertialContAssign(loop.params, loop.d, xition,
                                               loop.ctx, loop.arena);
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
  const std::function<void(const Logic4Vec&)>& commit;
};

// Waits out one pending transition, reporting through `*committed` whether the
// wait already drove the target. Only the module path route ever does, because
// §30.7's pulse filtering places two values on the output -- x and then the
// value the pulse returned to, or the pulse's own two edges. Every other wait
// leaves the single commit to the caller.
static ExecTask RunContAssignWait(const ContAssignWait& w, const Net* net,
                                  Logic4Vec& val, bool* committed) {
  ContAssignDelays d;
  if (w.params.delays.rise) {
    d = BuildContAssignDelays(w.params.delays, w.ctx, w.arena);
  }
  Logic4Vec old_val = CurrentContAssignOldValue(w.params, net, w.ctx, w.arena);
  uint64_t ticks = w.params.delays.rise
                       ? SelectContAssignDelay(old_val, val, d, w.params.width)
                       : 0;

  if (w.path_mgr != nullptr && !Logic4VecEqual(val, old_val)) {
    ModulePathDrive drive{
        w.ctx,       w.arena,      *w.path_mgr,    w.params.lhs->text,
        w.read_vars, w.params.rhs, w.params.width, ticks,
        w.commit};
    co_await RunModulePathTransition(drive, old_val, val, committed);
    co_return StmtResult::kDone;
  }

  if (ticks > 0 && !w.read_vars.empty()) {
    InertialLoopCtx loop{w.params, d, w.ctx, w.arena};
    co_await RunInertialContAssignDelay(loop, w.read_vars, old_val, val, ticks);
  } else if (ticks > 0) {
    co_await DelayAwaiter{w.ctx, ticks};
  }
  co_return StmtResult::kDone;
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
  CollectExprReads(params.rhs, read_strs);
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());

  auto* net = lhs_is_name ? ctx.FindNet(params.lhs->text) : nullptr;
  ContAssignDriver drv = MakeContAssignDriver(net);

  std::function<void(const Logic4Vec&)> commit = [&](const Logic4Vec& v) {
    CommitContAssignValue(params, drv, v, ctx, arena);
    drv.first = false;
  };

  // §30.4: a module path declared in a specify block delays whatever drives the
  // path output, and §30.7's pulse limits then decide what reaches it. The
  // manager is read here rather than at lowering because Lowerer::Lower
  // registers the specify blocks after it has lowered the modules; this body
  // first runs when the scheduler resumes it, by which time they are in.
  // `path_mgr` stays null for a target no module path names, which is every
  // target in a design that declared no specify block, and such a driver takes
  // exactly the route it took before.
  const SpecifyManager* spec = lhs_is_name ? ctx.GetSpecifyManager() : nullptr;
  const SpecifyManager* path_mgr =
      spec != nullptr && IsModulePathOutput(*spec, params.lhs->text) ? spec
                                                                     : nullptr;

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
    auto val = EvalExpr(params.rhs, ctx, arena, params.width);

    bool committed = false;
    if (params.delays.rise || path_mgr != nullptr) {
      ContAssignWait wait{params, ctx, arena, read_vars, path_mgr, commit};
      co_await RunContAssignWait(wait, net, val, &committed);
    }

    if (!committed) commit(val);

    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
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
  cap.ds = {ParserStrToStrength(ca.drive_strength0),
            ParserStrToStrength(ca.drive_strength1)};
  cap.nonresistive_switch = ca.from_nonresistive_switch;
  cap.resistive_switch = ca.from_resistive_switch;
  cap.data_input = ca.data_input;
  cap.delays = {ca.delay, ca.delay_fall, ca.delay_decay};
  cap.width = ca.width;
  p->coro = MakeContAssignCoroutine(cap, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_);
}
}  // namespace delta
