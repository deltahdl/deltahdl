// §28.8: lowering a bidirectional pass switch. The switch drives neither of
// its terminals from the other, so unlike every other gate it becomes no
// continuous assignment: its two nets are linked to it (Net::switch_links),
// and each resolves from the drivers it reaches across the switches that
// conduct (ResolveSwitchGroup in simulator/switch_network.h). What is lowered
// here is the switch's state, and for a tranif0, tranif1, rtranif0 or
// rtranif1 the process that follows its control with the turn-on and
// turn-off delays §28.8 gives it.

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir_primitives.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/switch_network.h"

namespace delta {

static BidirSwitchKind BidirKindOf(GateKind kind) {
  switch (kind) {
    case GateKind::kRtran:
      return BidirSwitchKind::kRtran;
    case GateKind::kTranif0:
      return BidirSwitchKind::kTranif0;
    case GateKind::kTranif1:
      return BidirSwitchKind::kTranif1;
    case GateKind::kRtranif0:
      return BidirSwitchKind::kRtranif0;
    case GateKind::kRtranif1:
      return BidirSwitchKind::kRtranif1;
    default:
      return BidirSwitchKind::kTran;
  }
}

// The net a bidirectional terminal names: a net by its name, or one reached
// by a hierarchical name (§23.6).
static Net* BidirTerminalNet(const Expr* e, SimContext& ctx) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier) return ctx.FindNet(e->text);
  if (e->kind == ExprKind::kMemberAccess) {
    return FindHierarchicalNet(e, ctx);
  }
  return nullptr;
}

// What the control process of one switch reads and writes.
struct BidirSwitchRun {
  BidirSwitchState* sw;
  Net* terminal;
  const Expr* control;
  const Expr* turn_on_delay;
  const Expr* turn_off_delay;
};

static uint8_t TargetState(const BidirSwitchRun& run, SimContext& ctx,
                           Arena& arena) {
  if (run.control == nullptr) return BidirSwitchState::kOn;
  Logic4Vec c = EvalExpr(run.control, ctx, arena);
  Logic4Word low = c.nwords > 0 ? c.words[0] : Logic4Word{0, 1};
  return BidirSwitchStateFor(run.sw->kind, low);
}

// §28.8: "If the specification contains two delays, the first delay shall
// determine the control input turn-on delay and the second delay shall
// determine the control input turn-off delay. For bidirectional switches
// connecting built-in net types, the smaller of the two delays shall apply to
// control input transitions to x and z. If only one delay is specified, it
// shall specify both the turn-on and the turn-off delays." A switch joining
// nets of user-defined net types is off for an x or z control, so it turns
// off after the turn-off delay.
static uint64_t TransitionDelay(const BidirSwitchRun& run, uint8_t target,
                                SimContext& ctx, Arena& arena) {
  BidirSwitchDelaySpec spec;
  if (run.turn_on_delay != nullptr) {
    spec.has_turn_on = true;
    spec.turn_on =
        DelayValueToTicks(EvalExpr(run.turn_on_delay, ctx, arena), ctx);
  }
  if (run.turn_off_delay != nullptr) {
    spec.has_turn_off = true;
    spec.turn_off =
        DelayValueToTicks(EvalExpr(run.turn_off_delay, ctx, arena), ctx);
  }
  if (target == BidirSwitchState::kOn) return BidirSwitchTurnOnDelay(spec);
  if (target == BidirSwitchState::kOff || run.sw->user_defined_nets) {
    return BidirSwitchTurnOffDelay(spec);
  }
  return BidirSwitchBuiltinControlXZDelay(spec);
}

// Resolves the switch's group once at the start, which a tran with nothing
// else to wait for does and is done, and then follows the control: each
// change that moves the switch to another state lands after the delay for
// that transition, the control being read again when it does, since §28.8
// puts the delay on the control input and a control that moved on meanwhile
// is where the switch goes next.
static SimCoroutine MakeBidirSwitchCoroutine(BidirSwitchRun run,
                                             SimContext& ctx, Arena& arena) {
  std::unordered_set<std::string> read_strs;
  if (run.control != nullptr) CollectExprReads(run.control, read_strs);
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());
  DropUnwatchableNames(ctx, read_vars);
  run.terminal->Resolve(arena, &ctx.GetScheduler());
  while (!ctx.StopRequested()) {
    uint8_t target = TargetState(run, ctx, arena);
    if (target != run.sw->state) {
      uint64_t ticks = TransitionDelay(run, target, ctx, arena);
      if (ticks > 0) {
        co_await DelayAwaiter{ctx, ticks};
        if (TargetState(run, ctx, arena) != target) continue;
      }
      run.sw->state = target;
      run.terminal->Resolve(arena, &ctx.GetScheduler());
    }
    if (read_vars.empty()) co_return;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
}

void Lowerer::LowerBidirSwitch(const RtlirBidirSwitch& sw, bool from_program) {
  Net* a = BidirTerminalNet(sw.terminal_a, ctx_);
  Net* b = BidirTerminalNet(sw.terminal_b, ctx_);
  if (a == nullptr || b == nullptr || a == b) return;
  auto* state = arena_.Create<BidirSwitchState>();
  state->kind = BidirKindOf(sw.kind);
  state->state =
      sw.control == nullptr ? BidirSwitchState::kOn : BidirSwitchState::kOff;
  state->user_defined_nets = a->is_user_nettype || b->is_user_nettype;
  a->switch_links.push_back({b, state});
  b->switch_links.push_back({a, state});

  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;
  p->home_region = from_program
                       ? Scheduler::HomeRegionForReactiveBlockingAssign()
                       : Region::kActive;
  p->is_reactive = from_program;
  p->inst_prefix = inst_prefix_;
  BidirSwitchRun run{state, a, sw.control, sw.turn_on_delay, sw.turn_off_delay};
  p->coro = MakeBidirSwitchCoroutine(run, ctx_, arena_).Release();
  ScheduleProcess(p, ctx_);
}

}  // namespace delta
