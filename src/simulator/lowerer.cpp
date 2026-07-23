#include "simulator/lowerer.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_child.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"

namespace delta {

Lowerer::Lowerer(SimContext& ctx, Arena& arena, DiagEngine&)
    : ctx_(ctx), arena_(arena) {}

static SimCoroutine MakeInitialCoroutine(const Stmt* body, SimContext& ctx,
                                         Arena& arena) {
  co_await ExecStmt(body, ctx, arena);
}

static SimCoroutine MakeProgramInitialCoroutine(const Stmt* body,
                                                SimContext& ctx, Arena& arena) {
  co_await ExecStmt(body, ctx, arena);
  ctx.OnProgramInitialComplete(ctx.CurrentProcess());
}

static SimCoroutine MakeAlwaysCoroutine(const Stmt* body, SimContext& ctx,
                                        Arena& arena) {
  while (!ctx.StopRequested()) {
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

static SimCoroutine MakeAlwaysSensCoroutine(const Stmt* body,
                                            const std::vector<EventExpr>& sens,
                                            SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, sens, arena};

    ctx.FlushPendingViolations();
    // §16.4.2: resuming after suspending on this event control is a deferred
    // assertion flush point; discard reports pending from before the suspend.
    ctx.FlushPendingDeferredReports();
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

// §9.2.2.2: a variable passed to an output formal of a called task/function is
// written by the call, not read. It must stay out of an always_comb's implicit
// sensitivity list; otherwise the block re-triggers on its own write and spins
// in a zero-delay loop. An inout actual is read as well as written, so only
// pure outputs are excluded. Callee formals come from the runtime subroutine
// registry, which is populated (RegisterModuleSubroutines) before processes are
// lowered.
// Records the base identifiers of any output actuals of a single call node.
static void CollectOutputActualsOfCall(const Expr* call, SimContext& ctx,
                                       std::unordered_set<std::string>& out) {
  const ModuleItem* fn = ctx.FindFunction(call->callee);
  if (!fn) return;
  size_t n = std::min(call->args.size(), fn->func_args.size());
  for (size_t i = 0; i < n; ++i) {
    if (fn->func_args[i].direction != Direction::kOutput) continue;
    const Expr* a = call->args[i];
    while (a && a->kind == ExprKind::kSelect && a->base) a = a->base;
    if (a && a->kind == ExprKind::kIdentifier && !a->text.empty())
      out.insert(std::string(a->text));
  }
}

static void CollectCallOutputActuals(const Expr* expr, SimContext& ctx,
                                     std::unordered_set<std::string>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty())
    CollectOutputActualsOfCall(expr, ctx, out);
  CollectCallOutputActuals(expr->lhs, ctx, out);
  CollectCallOutputActuals(expr->rhs, ctx, out);
  CollectCallOutputActuals(expr->condition, ctx, out);
  CollectCallOutputActuals(expr->true_expr, ctx, out);
  CollectCallOutputActuals(expr->false_expr, ctx, out);
  CollectCallOutputActuals(expr->base, ctx, out);
  CollectCallOutputActuals(expr->index, ctx, out);
  for (auto* arg : expr->args) CollectCallOutputActuals(arg, ctx, out);
  for (auto* elem : expr->elements) CollectCallOutputActuals(elem, ctx, out);
}

static void CollectCallOutputActuals(const Stmt* stmt, SimContext& ctx,
                                     std::unordered_set<std::string>& out) {
  if (!stmt) return;
  CollectCallOutputActuals(stmt->condition, ctx, out);
  CollectCallOutputActuals(stmt->rhs, ctx, out);
  CollectCallOutputActuals(stmt->expr, ctx, out);
  CollectCallOutputActuals(stmt->for_cond, ctx, out);
  CollectCallOutputActuals(stmt->assert_expr, ctx, out);
  for (auto* s : stmt->stmts) CollectCallOutputActuals(s, ctx, out);
  CollectCallOutputActuals(stmt->then_branch, ctx, out);
  CollectCallOutputActuals(stmt->else_branch, ctx, out);
  CollectCallOutputActuals(stmt->for_body, ctx, out);
  for (auto* fi : stmt->for_inits) CollectCallOutputActuals(fi, ctx, out);
  for (auto* fs : stmt->for_steps) CollectCallOutputActuals(fs, ctx, out);
  CollectCallOutputActuals(stmt->body, ctx, out);
  for (auto* s : stmt->fork_stmts) CollectCallOutputActuals(s, ctx, out);
  for (const auto& ci : stmt->case_items)
    CollectCallOutputActuals(ci.body, ctx, out);
}

static SimCoroutine MakeAlwaysCombCoroutine(const Stmt* body,
                                            const std::vector<EventExpr>& sens,
                                            SimContext& ctx, Arena& arena) {
  // §9.2.2.2.1: always_comb/always_latch watch the inferred sensitivity list,
  // which (unlike a raw read scan of the body) descends into called functions
  // and reduces each read to its base signal name -- so a variable read only
  // inside a called function still re-triggers the block, and a bit-select read
  // watches the whole vector. proc.sensitivity already excludes block-locals
  // and self-written signals; additionally drop any variable passed to a called
  // subroutine's output formal -- it is written by the call, not read, and
  // would otherwise re-trigger the block on its own update (a zero-delay spin).
  std::unordered_set<std::string> call_outputs;
  CollectCallOutputActuals(body, ctx, call_outputs);
  std::vector<std::string_view> read_vars;
  read_vars.reserve(sens.size());
  for (const auto& ev : sens) {
    if (!ev.signal || ev.signal->text.empty()) continue;
    if (call_outputs.count(std::string(ev.signal->text)) != 0) continue;
    read_vars.push_back(ev.signal->text);
  }
  while (!ctx.StopRequested()) {
    co_await ExecStmt(body, ctx, arena);
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};

    ctx.FlushPendingViolations();
    // §16.4.2: an always_comb/always_latch procedure re-running because a
    // dependent signal changed reaches a deferred assertion flush point on
    // resume, clearing any report queued by the superseded evaluation.
    ctx.FlushPendingDeferredReports();
  }
}

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
                                 Arena& arena) {
  if (drv.first) {
    drv.net->drivers.push_back(driven.value);
    drv.net->driver_strengths.push_back(driven.strength);
  } else {
    drv.net->drivers[drv.driver_idx] = driven.value;
    drv.net->driver_strengths[drv.driver_idx] = driven.strength;
  }
  drv.net->Resolve(arena);
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
    ApplyContAssignToNet(drv, driven, arena);
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

    if (params.delays.rise) {
      ContAssignDelays d = BuildContAssignDelays(params.delays, ctx, arena);
      Logic4Vec old_val = CurrentContAssignOldValue(params, net, ctx, arena);
      uint64_t ticks = SelectContAssignDelay(old_val, val, d, params.width);

      if (ticks > 0 && !read_vars.empty()) {
        InertialLoopCtx loop{params, d, ctx, arena};
        co_await RunInertialContAssignDelay(loop, read_vars, old_val, val,
                                            ticks);
      } else if (ticks > 0) {
        co_await DelayAwaiter{ctx, ticks};
      }
    }

    CommitContAssignValue(params, drv, val, ctx, arena);
    drv.first = false;

    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
}

static void ScheduleProcess(Process* proc, SimContext& ctx) {
  auto& sched = ctx.GetScheduler();
  auto* event = sched.GetEventPool().Acquire();

  event->kind = EventKind::kEvaluation;
  event->callback = [proc, &ctx]() {
    ctx.SetCurrentProcess(proc);
    proc->Resume();
  };
  sched.ScheduleEvent(SimTime{0}, proc->home_region, event);
}

void Lowerer::LowerProcesses(const std::vector<RtlirProcess>& procs,
                             bool from_program, uint32_t program_block_id) {
  for (const auto& proc : procs) {
    if (proc.kind != RtlirProcessKind::kInitial)
      LowerProcess(proc, from_program, program_block_id);
  }
  for (const auto& proc : procs) {
    if (proc.kind == RtlirProcessKind::kInitial)
      LowerProcess(proc, from_program, program_block_id);
  }
}

void Lowerer::LowerParams(const RtlirModule* mod) {
  for (const auto& p : mod->params) {
    // §23.10/§6.20: a parameter is an instance-specific runtime value, so its
    // variable is scoped by the instance prefix (empty for a top module). This
    // makes a child instance's parameters — including any defparam override —
    // visible to that instance's processes. The name is arena-persisted because
    // SimContext keys variables by string_view.
    auto* full = arena_.Create<std::string>(inst_prefix_ + std::string(p.name));
    if (p.is_unbounded) {
      ctx_.RegisterUnboundedParam(*full);
      ctx_.CreateVariable(*full, 32);
      continue;
    }
    if (!p.is_resolved) continue;
    // Use declared width if parameter has explicit type, else 32 (§10.8
    // context)
    uint32_t width = (p.decl_width > 0) ? p.decl_width : 32;
    auto* var = ctx_.CreateVariable(*full, width);
    var->value = MakeLogic4VecVal(arena_, width,
                                  static_cast<uint64_t>(p.resolved_value));
  }
}

void Lowerer::LowerAliases(const RtlirModule* mod) {
  for (const auto& alias : mod->aliases) {
    if (alias.nets.size() < 2) continue;
    std::string_view primary;
    for (auto* net : alias.nets) {
      if (net->kind != ExprKind::kIdentifier) continue;
      if (primary.empty()) {
        primary = net->text;
      } else {
        // §10.11: aliased nets denote the same physical net, so they share one
        // resolved storage. Redirect both the variable map (used for reads) and
        // the net map (used by continuous-assign driver resolution); otherwise
        // a driver on the non-primary net writes a Variable the alias never
        // sees.
        ctx_.AliasVariable(net->text, primary);
        ctx_.AliasNet(net->text, primary);
      }
    }
  }
}

void RegisterInstanceKeyBinding(const std::string& inst_prefix,
                                std::string_view library, std::string_view name,
                                SimContext& ctx) {
  std::string key = inst_prefix;
  if (!key.empty() && key.back() == '.') key.pop_back();
  ctx.RegisterInstanceType(key, name);
  // §33.7: record this instance's resolved library.cell so the %l/%L display
  // specifier can report its binding. The cell is the module's design-element
  // name; the library is the one it was compiled into.
  ctx.RegisterInstanceBinding(key, library, name);
}

static void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx) {
  for (const auto& net : mod->nets) {
    ctx.CreateNet(
        net.name, net.net_type, net.width,
        NetSpec{net.charge_strength, net.decay_ticks, net.is_user_nettype,
                net.resolve_func, net.is_signed});
  }
}

static void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx) {
  for (const auto& port : mod->ports) {
    if (!ctx.FindVariable(port.name)) {
      auto* v = ctx.CreateVariable(port.name, port.width);
      if (port.is_signed) v->is_signed = true;
      // §21.7.5 (Table 21-11): a port declared with a SystemVerilog data type
      // is dumped under that type's 1364-2005 masquerade, just as a module-body
      // declaration of the same type is. A port reaching here has no body
      // declaration that already recorded its kind, so record the declared
      // keyword now. The port carries only that keyword, so an enum port keeps
      // the default enum mapping rather than any specified base type.
      ctx.SetVcdVarKind(port.name, port.type_kind);
    }
  }
}

void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx) {
  for (auto* func : mod->function_decls) {
    ctx.RegisterFunction(func->name, func);
  }
  for (auto* let_decl : mod->let_decls) {
    ctx.RegisterLetDecl(let_decl->name, let_decl);
  }
}

static void RegisterModuleSequenceDecls(const RtlirModule* mod,
                                        SimContext& ctx) {
  for (auto* seq_decl : mod->sequence_decls) {
    ctx.RegisterSequenceDecl(seq_decl->name, seq_decl);

    std::string ep_name = std::string("__seq_") + std::string(seq_decl->name);
    if (!ctx.FindVariable(ep_name)) {
      // variables_ keys by string_view, so the key's backing string must
      // outlive the map; intern it in the arena. A local std::string would
      // dangle and make every later FindVariable("__seq_<name>") miss.
      auto* stored = ctx.GetArena().Create<std::string>(std::move(ep_name));
      auto* ep_var = ctx.CreateVariable(*stored, 1);
      ep_var->is_event = true;
    }
  }
}

static void RegisterProcessClassType(SimContext& ctx, Arena& arena) {
  auto* proc_type = arena.Create<ClassTypeInfo>();
  proc_type->name = "process";
  proc_type->enum_members["FINISHED"] = 0;
  proc_type->enum_members["RUNNING"] = 1;
  proc_type->enum_members["WAITING"] = 2;
  proc_type->enum_members["SUSPENDED"] = 3;
  proc_type->enum_members["KILLED"] = 4;
  ctx.RegisterClassType("process", proc_type);
}

void Lowerer::LowerModule(const RtlirModule* mod) {
  RegisterInstanceKeyBinding(inst_prefix_, mod->library, mod->name, ctx_);
  LowerParams(mod);
  RegisterModuleNets(mod, ctx_);
  RegisterEnumTypes(mod);
  // §8.7/§6.8: class types must be registered before module variables so a
  // class-handle declaration with a `new` static initializer (e.g.
  // `C h = new(42);`) can construct its object during static initialization.
  for (auto* cls : mod->class_decls) {
    LowerClassDecl(cls);
  }
  for (const auto& var : mod->variables) LowerVar(var);
  RegisterModulePorts(mod, ctx_);
  RegisterModuleSubroutines(mod, ctx_);
  RegisterModuleSequenceDecls(mod, ctx_);
  LowerSequenceMonitors(mod);

  LowerImports(mod);
  RegisterProcessClassType(ctx_, arena_);
  LowerAliases(mod);
  uint32_t program_block_id = mod->is_program ? next_program_block_id_++ : 0;
  LowerProcesses(mod->processes, mod->is_program, program_block_id);
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca, mod->is_program);
  }

  LowerChildModules(mod);
}

static void RegisterSensitivity(const RtlirProcess& proc, Process* p,
                                SimContext& ctx) {
  auto signals = CollectReadSignals(proc.body);
  for (const auto& name : signals) {
    ctx.AddSensitivity(name, p);
  }
}

void Lowerer::LowerProcess(const RtlirProcess& proc, bool from_program,
                           uint32_t program_block_id) {
  auto* p = arena_.Create<Process>();
  p->id = next_id_++;

  p->home_region = from_program
                       ? Scheduler::HomeRegionForReactiveBlockingAssign()
                       : Region::kActive;
  p->is_reactive = from_program;
  p->inst_prefix = inst_prefix_;
  // §18.14.1: a static process is seeded with the next value from the
  // enclosing initialization RNG. Lowering happens before any thread runs, so
  // the active stream here is the context-wide generator, which embodies the
  // module's initialization RNG for this test harness.
  p->rng_seed = ctx_.DrawSeedForChild();

  switch (proc.kind) {
    case RtlirProcessKind::kInitial:
      p->kind = ProcessKind::kInitial;
      if (from_program) {
        ctx_.RegisterProgramInitial(program_block_id, p);
        p->coro =
            MakeProgramInitialCoroutine(proc.body, ctx_, arena_).Release();
      } else {
        p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      }
      break;
    case RtlirProcessKind::kAlways:
      p->kind = ProcessKind::kAlways;
      if (!proc.sensitivity.empty() || proc.is_star_sensitivity) {
        p->coro =
            MakeAlwaysSensCoroutine(proc.body, proc.sensitivity, ctx_, arena_)
                .Release();
      } else {
        p->coro = MakeAlwaysCoroutine(proc.body, ctx_, arena_).Release();
      }
      break;
    case RtlirProcessKind::kAlwaysComb:
    case RtlirProcessKind::kAlwaysLatch:
      p->kind = ProcessKind::kAlwaysComb;
      p->coro =
          MakeAlwaysCombCoroutine(proc.body, proc.sensitivity, ctx_, arena_)
              .Release();
      RegisterSensitivity(proc, p, ctx_);
      break;
    case RtlirProcessKind::kAlwaysFF:
      // §9.2.2.4: an always_ff is driven by its explicit edge event control
      // (stored in proc.sensitivity), so it must wait on that event each
      // iteration like a sensitized always. Using the always_comb re-trigger
      // loop instead made it re-fire on its own nonblocking-assign updates and
      // spin forever.
      p->kind = ProcessKind::kAlwaysFF;
      p->coro =
          MakeAlwaysSensCoroutine(proc.body, proc.sensitivity, ctx_, arena_)
              .Release();
      break;
    case RtlirProcessKind::kFinal:
      p->kind = ProcessKind::kFinal;
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      ctx_.RegisterFinalProcess(p);
      return;
  }

  ScheduleProcess(p, ctx_);
}

// §16.13.6/§9.4.4: spawn a monitor process for each named sequence whose simple
// clocked linear body the parser captured, so its endpoint event fires on a
// match and procedural `sequence.triggered`/`wait` observe it. Additive: no
// other code fires these endpoint events.
void Lowerer::LowerSequenceMonitors(const RtlirModule* mod) {
  for (auto* seq : mod->sequence_decls) {
    if (seq->seq_clock.empty() || seq->seq_linear_operands.empty()) continue;
    auto* p = arena_.Create<Process>();
    p->kind = ProcessKind::kAlways;
    p->id = next_id_++;
    p->home_region = Region::kActive;
    p->inst_prefix = inst_prefix_;
    p->rng_seed = ctx_.DrawSeedForChild();
    p->coro = MakeSequenceMonitorCoroutine(seq, ctx_, arena_).Release();
    ScheduleProcess(p, ctx_);
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

static void RegisterDesignTypeWidths(const RtlirDesign* design,
                                     SimContext& ctx) {
  for (const auto& [name, width] : design->type_widths) {
    ctx.RegisterTypeWidth(name, width);
  }
}

static void InitPackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                                     Arena& arena) {
  for (auto* pkg : design->packages) {
    for (auto* item : pkg->items) {
      bool is_param = item->kind == ModuleItemKind::kParamDecl;
      bool is_var = item->kind == ModuleItemKind::kVarDecl;
      if (!(is_param || is_var) || !item->init_expr) continue;
      auto* qname = arena.Create<std::string>(std::string(pkg->name) + "." +
                                              std::string(item->name));
      auto* var = ctx.CreateVariable(*qname, 32);
      var->value = EvalExpr(item->init_expr, ctx, arena);
    }
  }
}

// §20.4.1: publish each design element's resolved timescale under its module
// name and instance name so a $timeunit/$timeprecision argument that names the
// element (e.g. $timeunit(dut)) reports that element's value.
static void RegisterScopeTimescales(const RtlirModule* mod, SimContext& ctx) {
  ctx.SetScopeTimeScale(mod->name, mod->timescale);
  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    ctx.SetScopeTimeScale(child.inst_name, child.resolved->timescale);
    RegisterScopeTimescales(child.resolved, ctx);
  }
}

static void RegisterFreeCuFunctions(const RtlirDesign* design,
                                    SimContext& ctx) {
  for (auto* item : design->cu_function_decls) {
    if (!item->method_class.empty()) continue;
    ctx.RegisterFunction(item->name, item);
  }
}

static void AttachCuMethodsToClasses(const RtlirDesign* design,
                                     SimContext& ctx) {
  for (auto* item : design->cu_function_decls) {
    if (item->method_class.empty()) continue;
    auto* cls = ctx.FindClassType(item->method_class);
    if (!cls) continue;
    std::string name(item->name);
    // 8.24: the out-of-block definition repeats neither the lifetime nor the
    // static qualifier, so the body item parses with is_static false. Carry the
    // static-ness forward from the in-class prototype before the body replaces
    // it, so a class-scoped call (C#()::f()) still resolves it as static.
    auto existing = cls->methods.find(name);
    if (existing != cls->methods.end() && existing->second->is_static) {
      item->is_static = true;
    }
    cls->methods[name] = item;
  }
}

void Lowerer::Lower(const RtlirDesign* design) {
  if (!design) return;
  // §20.10.1: a $fatal or $error elaboration severity task that survived
  // generate expansion marks the design as not startable. Refuse to lower
  // any part of it so the scheduler sees an empty event calendar.
  if (design->simulation_blocked) return;
  design_ = design;
  // Annex D.11: the interactive scope consulted by the optional $scope system
  // task starts at the first top-level module. A later $scope call retargets
  // it.
  if (!design->top_modules.empty()) {
    ctx_.SetInteractiveScope(design->top_modules.front()->name);
  }
  // §20.4.1 / §3.14.3: seed the runtime timescale state read by
  // $timeunit/$timeprecision. The simulation time unit and compilation-unit
  // timescale come from the design; the top module is the initial current
  // scope reported when those functions take no argument.
  ctx_.SetGlobalPrecision(design->global_time_precision);
  ctx_.SetCompUnitTimeScale(design->cu_timescale);
  if (!design->top_modules.empty()) {
    const RtlirModule* top = design->top_modules.front();
    ctx_.SetCurrentTimeScale(top->timescale);
    ctx_.SetCurrentScopeName(top->name);
  }
  for (auto* top : design->top_modules) {
    RegisterScopeTimescales(top, ctx_);
  }
  RegisterDesignTypeWidths(design, ctx_);
  InitPackageDataVariables(design, ctx_, arena_);

  for (auto* cls : design->cu_class_decls) {
    if (!ctx_.FindClassType(cls->name)) {
      LowerClassDecl(cls);
    }
  }

  RegisterFreeCuFunctions(design, ctx_);
  for (auto* mod : design->top_modules) {
    LowerModule(mod);
  }

  for (auto* let_decl : design->cu_let_decls) {
    ctx_.RegisterLetDecl(let_decl->name, let_decl);
  }

  AttachCuMethodsToClasses(design, ctx_);
}

}  // namespace delta
