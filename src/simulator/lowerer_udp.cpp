// §29.8: lowering a user-defined primitive instance into the process that
// drives its output terminal.
//
// "Instances of UDPs are specified inside modules in the same manner as gates
// (see 28.3)", and a gate reaches the simulator as a driver on the net its
// output terminal names, so a primitive does too. What it drives is what the
// state table §29.3.4 defines says, and UdpEvalState in
// src/simulator/udp_eval.h is what answers that table. This file is the join
// between the two: it reads the instance's input terminals into the positional
// vector that evaluator takes, applies the delay2 §29.8 admits, and commits the
// result to the output terminal with the drive strengths the instance carries.
//
// The process is created here and started by ScheduleProcess, which
// src/simulator/lowerer.h declares and src/simulator/lowerer.cpp defines. That
// is how §10.3's continuous assignments are started too, which is what §29.8's
// "in the same manner as gates" comes to at run time.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/udp_eval.h"

namespace delta {

// The strength one half of a drive_strength names, from the code the parser
// records on the instance. §28.11 gives the four driving strengths supply,
// strong, pull and weak, and a drive_strength may also name highz; code 4 is
// strong and so is code 0, which is what the parser leaves where the source
// wrote no drive_strength at all.
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

// The one bit a primitive drives, in the 4-state encoding a net holds:
// (aval, bval) is (0,0) for 0, (1,0) for 1, (1,1) for x and (0,1) for z.
// UdpEvalState answers '0', '1' or 'x' and never 'z', because §29.3.4 rules
// that "The z state is explicitly excluded from consideration in UDPs" and
// §29.3.5 treats a z passed to an input terminal the same as an x. So z reaches
// the net only through a highz drive strength, which §28.11 makes a driver that
// is off for the value it names.
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

// The value one input terminal contributes to the state table, as the character
// UdpEvalState matches a row against. §29.3.1 rules that "All ports of a UDP
// shall be scalar; vector ports are not permitted", so a terminal is one bit:
// the expression is evaluated in a one-bit context and its least significant
// bit is what the table sees. Logic4Vec::ToString spells a vector most
// significant bit first, so that bit is the last character of the spelling.
static char UdpInputChar(const Expr* terminal, SimContext& ctx, Arena& arena) {
  std::string bits = EvalExpr(terminal, ctx, arena, 1).ToString();
  return bits.empty() ? 'x' : bits.back();
}

// The input terminals of one instance, in the order the state table indexes
// them. §29.3.4 rules that "The order of the input state fields of each row of
// the state table is taken directly from the port list in the UDP definition
// header", and §29.8 rules that "The terminal connection order is as specified
// in the UDP definition", so position i of this vector is position i of every
// row.
static std::vector<char> ReadUdpInputs(const RtlirUdpInst& inst,
                                       SimContext& ctx, Arena& arena) {
  std::vector<char> inputs;
  inputs.reserve(inst.inputs.size());
  for (const Expr* terminal : inst.inputs) {
    inputs.push_back(UdpInputChar(terminal, ctx, arena));
  }
  return inputs;
}

// The driver a primitive instance holds on the net its output terminal names.
// §29.8 instantiates a UDP "in the same manner as gates", so the instance is
// one driver of that net and §28.11's resolution decides what the net settles
// at. The slot is appended by the first commit and overwritten by every later
// one, which is what `first` distinguishes; `strength` is the instance's
// drive_strength, which is fixed for the run.
struct UdpOutputDriver {
  Net* net = nullptr;
  DriverStrength strength;
  std::size_t idx = 0;
  bool first = true;
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

static void CommitUdpOutput(const Expr* terminal, UdpOutputDriver* drv,
                            char out, SimContext& ctx, Arena& arena) {
  Logic4Vec val = UdpDrivenBit(out, drv->strength, arena);
  if (drv->net == nullptr) {
    // A terminal that is not a whole net -- a select, which §29.8 admits by
    // keeping "the terminal connection rules ... the same as outlined in
    // 28.3.6" -- has no driver slot of its own, so it is written through the
    // procedural lvalue writer, which decomposes the lvalue and notifies each
    // affected variable's watchers (§11.4.1).
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
  // §28.16.2.1: the scheduler is passed so Resolve can arm a trireg's charge
  // decay process where this update leaves the net with only high-impedance
  // drivers.
  drv->net->Resolve(arena, &ctx.GetScheduler());
}

// How long a transition to `out` waits before it reaches the output terminal.
// §29.8 admits a delay2 on a primitive instance and rules that "Only two delays
// may be specified because z is not supported for UDPs", so this is the one-bit
// case of Table 28-9 in §28.16 with the third, turn-off delay of that table
// absent: a transition to 1 waits the rise delay, one to 0 the fall delay, and
// one to x the lesser of the two. Where the source wrote a single delay, §28.16
// rules that "this value shall be used for all propagation delays associated
// with the gate or the net".
static uint64_t SelectUdpDelay(const RtlirUdpInst& inst, char out,
                               SimContext& ctx, Arena& arena) {
  if (inst.delay == nullptr) return 0;
  uint64_t rise = EvalExpr(inst.delay, ctx, arena).ToUint64();
  if (inst.delay_fall == nullptr) return rise;
  uint64_t fall = EvalExpr(inst.delay_fall, ctx, arena).ToUint64();
  if (out == '0') return fall;
  if (out == '1') return rise;
  return std::min(rise, fall);
}

// Puts `out` on the output terminal, after the delay §28.16 selects for it.
//
// A delay is served by a scheduled update event rather than by suspending the
// process, so that the process stays on its watch of the input terminals for
// the whole of the delay. §29.6 triggers a change of the output on a transition
// of an input, and a primitive whose delay is longer than the interval between
// two such transitions has to see both; a process parked on the delay would see
// only the first, because the watch is re-armed after the delay elapses and a
// transition in between reaches nothing.
static void DriveUdpOutput(const RtlirUdpInst& inst, UdpOutputDriver* drv,
                           char out, SimContext& ctx, Arena& arena) {
  uint64_t ticks = SelectUdpDelay(inst, out, ctx, arena);
  if (ticks == 0) {
    CommitUdpOutput(inst.output, drv, out, ctx, arena);
    return;
  }
  const Expr* terminal = inst.output;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  // §4.4: putting a new value on a net is an update event.
  event->kind = EventKind::kUpdate;
  event->callback = [terminal, drv, out, &ctx, &arena]() {
    CommitUdpOutput(terminal, drv, out, ctx, arena);
  };
  // §24.3.1: an instance written in a program drives in the Reactive region,
  // which is the region the process this runs in was given.
  Region region = ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime() + SimTime{ticks}, region,
                                   event);
}

// Runs the state table once for every input terminal that moved since the
// previous snapshot, and answers the output the last of those runs left. §29.6
// rules that "Each table entry can have a transition specification on at most
// one input", so a row is matched against one transition: two terminals moving
// between one evaluation and the next are two runs of the table rather than
// one, taken in terminal order. Where no terminal moved there is no transition
// to trigger a change of the output (§29.6), so the output stands.
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

// The output the primitive shows for the values now on its input terminals.
//
// A sequential primitive is matched against the transitions that brought its
// terminals here, because §29.6 rules that "changes in the output are triggered
// by specific transitions of the inputs. This makes the state table a
// transition table", and because §29.5 makes the current state field "the same
// as the internal state" the previous run left. A combinational primitive has
// no current state field, so §29.4's form matches the input levels alone.
static char UdpPassOutput(UdpEvalState& state, bool is_sequential,
                          const std::vector<char>& prev,
                          const std::vector<char>& now) {
  if (is_sequential) return EvaluateSequentialUdp(state, prev, now);
  return state.Evaluate(now);
}

// `inst` is held by pointer rather than copied because this coroutine outlives
// the call that creates it: it first runs when the scheduler resumes it. The
// RtlirUdpInst is a member of the RtlirModule the RtlirDesign holds, and
// RunSimulation in src/main.cpp keeps that design alive across
// Scheduler::Run(), which is the lifetime the Expr pointers of a lowered
// process already rely on.
static SimCoroutine MakeUdpInstCoroutine(const RtlirUdpInst* inst,
                                         SimContext& ctx, Arena& arena) {
  if (inst->decl == nullptr || inst->output == nullptr) co_return;

  // The change-watchers and SimContext key by std::string_view, so the strings
  // backing read_vars must outlive every co_await below. The owning set is kept
  // in the coroutine frame for that reason, as MakeContAssignCoroutine's is.
  std::unordered_set<std::string> read_strs;
  for (const Expr* terminal : inst->inputs) {
    CollectExprReads(terminal, read_strs);
  }
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());

  // One evaluator for the life of the instance. §29.5 makes the current state
  // of a sequential primitive the current output value, so a UdpEvalState built
  // per evaluation would match every row against the initial value §29.7 gives
  // rather than against the state the previous evaluation left.
  UdpEvalState state(*inst->decl);
  // The driver lives in the arena rather than in this coroutine frame because a
  // delayed commit is a scheduler event that runs after this coroutine has
  // moved on to its next evaluation.
  auto* drv = arena.Create<UdpOutputDriver>(MakeUdpOutputDriver(*inst, ctx));

  // §29.7: "When simulation starts, this value is the current state in the
  // state table", and "a delay specification on an instantiated UDP does not
  // delay the simulation time of the assignment of this initial value to the
  // output". So a sequential primitive drives what its initial statement gave
  // before any table is consulted, whatever delay the instance carries. A
  // combinational primitive has no such value, since §29.3.2 rules that
  // "Combinational UDPs cannot contain a reg declaration" and §29.3.3's initial
  // statement assigns to that reg.
  if (inst->decl->is_sequential) {
    CommitUdpOutput(inst->output, drv, state.GetOutput(), ctx, arena);
  }

  // The terminals are taken to have stood at x before the run began, which is
  // the value §6.8 gives an unassigned 4-state variable and the value §29.3.5
  // gives an input terminal left at z. So the first evaluation sees the
  // transitions that brought the terminals to the values they now hold, rather
  // than seeing no transition at all -- which is what a level-sensitive
  // sequential primitive needs to leave its initial state at time zero.
  std::vector<char> prev_inputs(inst->inputs.size(), 'x');
  while (true) {
    std::vector<char> inputs = ReadUdpInputs(*inst, ctx, arena);
    char out =
        UdpPassOutput(state, inst->decl->is_sequential, prev_inputs, inputs);
    DriveUdpOutput(*inst, drv, out, ctx, arena);
    prev_inputs = std::move(inputs);
    // An instance whose terminals read no name can never see a transition, so
    // §29.6 leaves nothing that could change its output again.
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};
    if (ctx.StopRequested()) break;
  }
}

void Lowerer::LowerUdpInst(const RtlirUdpInst& inst, bool from_program) {
  auto* p = arena_.Create<Process>();
  // §29.8 instantiates a UDP "in the same manner as gates", and a gate drives
  // its output net continuously rather than as a procedure §9.2 declares. That
  // is what ProcessKind::kContAssign says, and it is what makes this process an
  // invalid target for the process control of §9.7.
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;
  p->home_region = from_program
                       ? Scheduler::HomeRegionForReactiveBlockingAssign()
                       : Region::kActive;
  p->is_reactive = from_program;
  p->inst_prefix = inst_prefix_;
  p->gen_prefix = std::string(inst.gen_block_prefix);
  InstallGenBlockConsts(inst.gen_block_consts, p);
  p->coro = MakeUdpInstCoroutine(&inst, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_);
}

}  // namespace delta
