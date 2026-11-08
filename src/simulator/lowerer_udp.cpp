#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir_primitives.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/udp_eval.h"

namespace delta {

static Strength UdpDriveStrength(uint8_t code) {
  switch (code) {
    case 1:
      return Strength::kHighz;
    case 2:
      return Strength::kWeak;
    case 3:
      return Strength::kPull;
    case 5:
      return Strength::kSupply;
    default:
      return Strength::kStrong;
  }
}

static Logic4Vec UdpDrivenBit(char out, DriverStrength ds, Arena& arena) {
  bool off = (out == '0' && ds.s0 == Strength::kHighz) ||
             (out == '1' && ds.s1 == Strength::kHighz);
  if (off) {
    Logic4Vec z = MakeLogic4VecVal(arena, 1, 0);
    z.words[0].bval = 1;
    return z;
  }
  if (out == '0') return MakeLogic4VecVal(arena, 1, 0);
  if (out == '1') return MakeLogic4VecVal(arena, 1, 1);
  return MakeAllX(arena, 1);
}

static char UdpInputChar(const Expr* terminal, SimContext& ctx, Arena& arena) {
  std::string bits = EvalExpr(terminal, ctx, arena, 1).ToString();
  return bits.empty() ? 'x' : bits.back();
}

static char UdpInitialOutput(const UdpDecl& decl, SimContext& ctx,
                             Arena& arena) {
  if (decl.initial_expr == nullptr) return decl.initial_value;
  char bit = UdpInputChar(decl.initial_expr, ctx, arena);
  return bit == 'z' ? 'x' : bit;
}

static std::vector<char> ReadUdpInputs(const RtlirUdpInst& inst,
                                       SimContext& ctx, Arena& arena) {
  std::vector<char> inputs;
  inputs.reserve(inst.inputs.size());
  for (const Expr* terminal : inst.inputs) {
    const char kBit = UdpInputChar(terminal, ctx, arena);
    inputs.push_back(kBit == 'z' ? 'x' : kBit);
  }
  return inputs;
}

struct UdpOutputDriver {
  Net* net = nullptr;
  DriverStrength strength;
  std::size_t idx = 0;
  bool first = true;
  bool partial = false;
  uint32_t bit = 0;
  char committed = 0;
  char pending = 0;
  uint64_t generation = 0;
  UdpEvalState* state = nullptr;
  std::string inst_prefix;
};

static UdpOutputDriver MakeUdpOutputDriver(const RtlirUdpInst& inst,
                                           SimContext& ctx) {
  UdpOutputDriver drv;
  drv.strength = {UdpDriveStrength(inst.drive_strength0),
                  UdpDriveStrength(inst.drive_strength1)};
  if (inst.output->kind == ExprKind::kIdentifier) {
    drv.net = ctx.FindNet(inst.output->text);
  }
  return drv;
}

static void FindUdpSelectOutput(const Expr* output, UdpOutputDriver* drv,
                                SimContext& ctx) {
  if (output->kind != ExprKind::kSelect) return;
  drv->net = ctx.FindNet(output->base->text);
  drv->partial = drv->net != nullptr;
  if (!drv->partial) return;
  int64_t index =
      SelectBoundValue(EvalExpr(output->index, ctx, ctx.GetArena()));
  drv->bit = static_cast<uint32_t>(
      drv->net->resolved->DeclaredRange().OffsetOf(index));
}

static void CommitUdpOutput(const Expr* terminal, UdpOutputDriver* drv,
                            char out, SimContext& ctx, Arena& arena) {
  drv->committed = out;
  Logic4Vec val = UdpDrivenBit(out, drv->strength, arena);
  if (drv->partial) {
    Logic4Vec whole = MakeAllHighZ(arena, drv->net->resolved->value.width);
    DepositBitField(whole, drv->bit, val, 1);
    val = whole;
  }
  if (drv->net == nullptr) {
    PerformBlockingAssign(terminal, val, ctx, arena);
    return;
  }
  if (drv->first) {
    drv->idx = drv->net->drivers.size();
    drv->net->drivers.push_back(val);
    drv->net->driver_strengths.push_back(drv->strength);
    drv->first = false;
  } else {
    drv->net->drivers[drv->idx] = val;
    drv->net->driver_strengths[drv->idx] = drv->strength;
  }
  drv->net->Resolve(arena, &ctx.GetScheduler());
}

static void PutUdpState(const Expr* terminal, UdpOutputDriver* drv, char bit,
                        SimContext& ctx, Arena& arena) {
  drv->state->SetOutput(bit);
  ++drv->generation;
  drv->pending = 0;
  CommitUdpOutput(terminal, drv, bit, ctx, arena);
}

static const PrimitiveDriver* PutUdpDelays(const RtlirUdpInst& inst,
                                           const UdpOutputDriver& drv,
                                           SimContext& ctx) {
  const SpecifyManager* specify = ctx.GetSpecifyManager();
  const Expr* output = inst.output;
  if (specify == nullptr || output == nullptr) return nullptr;
  if (output->kind == ExprKind::kSelect) output = output->base;
  if (output == nullptr || output->kind != ExprKind::kIdentifier)
    return nullptr;
  return specify->FindAnnotatedPrimitiveDriver(drv.inst_prefix, output->text);
}

static uint64_t SelectUdpDelay(const RtlirUdpInst& inst,
                               const UdpOutputDriver& drv, char out,
                               SimContext& ctx, Arena& arena) {
  uint64_t rise = 0;
  uint64_t fall = 0;
  if (const PrimitiveDriver* put = PutUdpDelays(inst, drv, ctx)) {
    rise = put->delays[0];
    fall = put->delays[1];
  } else {
    if (inst.delay == nullptr) return 0;
    rise = DelayExprToTicks(inst.delay, ctx, arena);
    if (inst.delay_fall == nullptr) return rise;
    fall = DelayExprToTicks(inst.delay_fall, ctx, arena);
  }
  if (out == '0') return fall;
  if (out == '1') return rise;
  return std::min(rise, fall);
}

static void DriveUdpOutput(const RtlirUdpInst& inst, UdpOutputDriver* drv,
                           char out, SimContext& ctx, Arena& arena) {
  if (drv->pending == out) return;
  ++drv->generation;
  drv->pending = 0;
  if (out == drv->committed) return;
  uint64_t ticks = SelectUdpDelay(inst, *drv, out, ctx, arena);
  if (ticks == 0) {
    CommitUdpOutput(inst.output, drv, out, ctx, arena);
    return;
  }
  drv->pending = out;
  uint64_t gen = drv->generation;
  const Expr* terminal = inst.output;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->kind = EventKind::kUpdate;
  event->callback = [terminal, drv, out, gen, &ctx, &arena]() {
    if (drv->generation != gen) return;
    drv->pending = 0;
    CommitUdpOutput(terminal, drv, out, ctx, arena);
  };
  Region region = ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime() + SimTime{ticks}, region,
                                   event);
}

static char EvaluateSequentialUdp(UdpEvalState& state,
                                  const std::vector<char>& prev,
                                  const std::vector<char>& now) {
  std::vector<char> snapshot = prev;
  for (std::size_t i = 0; i < now.size() && i < snapshot.size(); ++i) {
    if (snapshot[i] == now[i]) continue;
    char was = snapshot[i];
    snapshot[i] = now[i];
    state.EvaluateWithEdge(snapshot, static_cast<uint32_t>(i), was);
  }
  return state.GetOutput();
}

static char UdpPassOutput(UdpEvalState& state, bool is_sequential,
                          const std::vector<char>& prev,
                          const std::vector<char>& now) {
  if (is_sequential) return EvaluateSequentialUdp(state, prev, now);
  return state.Evaluate(now);
}

static SimCoroutine MakeUdpInstCoroutine(const RtlirUdpInst* inst,
                                         UdpOutputDriver* drv, SimContext& ctx,
                                         Arena& arena) {
  if (inst->decl == nullptr || inst->output == nullptr) co_return;

  std::unordered_set<std::string> read_strs;
  for (const Expr* terminal : inst->inputs) {
    CollectExprReads(terminal, read_strs);
  }
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());
  DropUnwatchableNames(ctx, read_vars);

  UdpEvalState& state = *drv->state;
  FindUdpSelectOutput(inst->output, drv, ctx);

  if (inst->decl->is_sequential && drv->first) {
    CommitUdpOutput(inst->output, drv, state.GetOutput(), ctx, arena);
  }

  std::vector<char> prev_inputs(inst->inputs.size(), 'x');
  while (true) {
    std::vector<char> inputs = ReadUdpInputs(*inst, ctx, arena);
    char out =
        UdpPassOutput(state, inst->decl->is_sequential, prev_inputs, inputs);
    DriveUdpOutput(*inst, drv, out, ctx, arena);
    prev_inputs = std::move(inputs);
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};
    if (ctx.StopRequested()) break;
  }
}

static void RegisterUdpStateSetter(const RtlirUdpInst& inst,
                                   UdpOutputDriver* drv,
                                   const std::string& inst_prefix,
                                   SimContext& ctx, Arena& arena) {
  if (!inst.decl->is_sequential || inst.name.empty()) return;
  std::string name = inst_prefix + std::string(inst.name);
  if (inst.array_index) name += std::format("[{}]", *inst.array_index);
  ctx.UdpStateSetters()[name] = [output = inst.output, drv, &ctx,
                                 &arena](char bit) {
    PutUdpState(output, drv, bit, ctx, arena);
  };
}

void Lowerer::LowerUdpInst(const RtlirUdpInst& inst, bool from_program) {
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;
  p->home_region = from_program
                       ? Scheduler::HomeRegionForReactiveBlockingAssign()
                       : Region::kActive;
  p->is_reactive = from_program;
  p->inst_prefix = inst_prefix_;
  p->gen_prefixes.assign(inst.gen_block_prefixes.begin(),
                         inst.gen_block_prefixes.end());
  InstallGenBlockConsts(inst.gen_block_consts, p);
  UdpOutputDriver* drv = nullptr;
  if (inst.decl != nullptr && inst.output != nullptr) {
    drv = arena_.Create<UdpOutputDriver>(MakeUdpOutputDriver(inst, ctx_));
    drv->inst_prefix = inst_prefix_;
    const char kInitial = UdpInitialOutput(*inst.decl, ctx_, arena_);
    drv->state = arena_.Create<UdpEvalState>(*inst.decl, kInitial);
    if (inst.decl->is_sequential && drv->net != nullptr) {
      CommitUdpOutput(inst.output, drv, kInitial, ctx_, arena_);
    }
    RegisterUdpStateSetter(inst, drv, inst_prefix_, ctx_, arena_);
  }
  p->coro = MakeUdpInstCoroutine(&inst, drv, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_);
}

}  // namespace delta
