#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
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

static Net* BidirTerminalNet(const Expr* e, SimContext& ctx) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier) return ctx.FindNet(e->text);
  if (e->kind == ExprKind::kMemberAccess) {
    return FindHierarchicalNet(e, ctx);
  }
  return nullptr;
}

struct BidirTerminal {
  Net* net = nullptr;
  std::optional<uint32_t> bit;
};

static BidirTerminal ResolveBidirTerminal(const Expr* e, SimContext& ctx,
                                          Arena& arena) {
  if (e->kind != ExprKind::kSelect) return {BidirTerminalNet(e, ctx), {}};
  Net* net = BidirTerminalNet(e->base, ctx);
  if (net == nullptr) return {};
  int64_t index = SelectBoundValue(EvalExpr(e->index, ctx, arena));
  PackedRange range = net->resolved->DeclaredRange();
  if (!range.Contains(index)) return {};
  return {net, static_cast<uint32_t>(range.OffsetOf(index))};
}

static const std::vector<std::pair<uint32_t, uint32_t>>* TerminalBitMap(
    const BidirTerminal& from, const BidirTerminal& to, Arena& arena) {
  if (!from.bit && !to.bit) return nullptr;
  return arena.Create<std::vector<std::pair<uint32_t, uint32_t>>>(
      std::vector<std::pair<uint32_t, uint32_t>>{
          {from.bit.value_or(0), to.bit.value_or(0)}});
}

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

static uint64_t TransitionDelay(const BidirSwitchRun& run, uint8_t target,
                                SimContext& ctx, Arena& arena) {
  BidirSwitchDelaySpec spec;
  if (run.turn_on_delay != nullptr) {
    spec.has_turn_on = true;
    spec.turn_on = DelayExprToTicks(run.turn_on_delay, ctx, arena);
  }
  if (run.turn_off_delay != nullptr) {
    spec.has_turn_off = true;
    spec.turn_off = DelayExprToTicks(run.turn_off_delay, ctx, arena);
  }
  if (target == BidirSwitchState::kOn) return BidirSwitchTurnOnDelay(spec);
  if (target == BidirSwitchState::kOff || run.sw->user_defined_nets) {
    return BidirSwitchTurnOffDelay(spec);
  }
  return BidirSwitchBuiltinControlXZDelay(spec);
}

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
  BidirTerminal ta = ResolveBidirTerminal(sw.terminal_a, ctx_, arena_);
  BidirTerminal tb = ResolveBidirTerminal(sw.terminal_b, ctx_, arena_);
  Net* a = ta.net;
  Net* b = tb.net;
  if (a == nullptr || b == nullptr || (a == b && ta.bit == tb.bit)) return;
  auto* state = arena_.Create<BidirSwitchState>();
  state->kind = BidirKindOf(sw.kind);
  state->state =
      sw.control == nullptr ? BidirSwitchState::kOn : BidirSwitchState::kOff;
  state->user_defined_nets = a->is_user_nettype || b->is_user_nettype;
  a->switch_links.push_back({b, state, TerminalBitMap(ta, tb, arena_)});
  b->switch_links.push_back({a, state, TerminalBitMap(tb, ta, arena_)});

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
