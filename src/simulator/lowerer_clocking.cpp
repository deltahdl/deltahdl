#include <optional>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// §14.3's clocking_direction in the terms ClockingManager keeps. An `inout`
// clockvar is sampled like an input and driven like an output, so it stays its
// own direction rather than collapsing into either; a signal that states no
// direction reads as an input, which is what the clause's default skew rules
// are written about.
ClockingDir ClockingDirOf(Direction dir) {
  if (dir == Direction::kOutput) return ClockingDir::kOutput;
  if (dir == Direction::kInout) return ClockingDir::kInout;
  return ClockingDir::kInput;
}

// §14.4: "the default input skew is 1step", which names the value the signal
// held in the time step before the clocking event rather than a delay measured
// after it. The parser writes that skew as a literal spelled `1step`
// (Parser::ParseClockingSkew), and the mark travels with the signal because
// ClockingManager reads a recorded previous-step value for it and an elapsed
// skew for every other.
bool IsOneStepSkew(const Expr* delay) {
  return delay != nullptr && delay->text == "1step";
}

// §14.4's clocking skew as a number of time units. The clause makes a skew "a
// constant expression", which elaboration has already checked
// (Elaborator::ValidateClockingBlock), so it is folded here against the context
// the design is being lowered into. A 1step skew measures no delay at all and
// is carried by the mark above instead.
SimTime ClockingSkewOf(const Expr* delay, SimContext& ctx, Arena& arena) {
  if (delay == nullptr || IsOneStepSkew(delay)) return SimTime{0};
  return SimTime{EvalExpr(delay, ctx, arena).ToUint64()};
}

// §14.3 gives each clocking_item an optional clocking_skew and §14.4 has the
// block's default_skew stand for the items that omit one, so the skew governing
// one item is its own where it wrote one and the block's otherwise. An output
// item carries its skew in ClockingSignalDecl::skew_delay when the direction is
// output-only and in out_skew_delay when the item is an inout
// (Parser::MakeClockingSignal), so both are read for a driven signal.
const Expr* SkewExprOf(const ClockingSignalDecl& decl, const ModuleItem* item,
                       ClockingDir dir) {
  if (dir == ClockingDir::kInput) {
    return decl.skew_delay != nullptr ? decl.skew_delay
                                      : item->default_input_skew_delay;
  }
  const Expr* own =
      decl.out_skew_delay != nullptr ? decl.out_skew_delay : decl.skew_delay;
  return own != nullptr ? own : item->default_output_skew_delay;
}

ClockingSignal ClockingSignalOf(const ClockingSignalDecl& decl,
                                const ModuleItem* item, SimContext& ctx,
                                Arena& arena) {
  ClockingSignal sig;
  sig.signal_name = decl.name;
  sig.direction = ClockingDirOf(decl.direction);
  const Expr* skew = SkewExprOf(decl, item, sig.direction);
  sig.skew = ClockingSkewOf(skew, ctx, arena);
  sig.is_one_step_skew = IsOneStepSkew(skew);
  // §14.4: an explicit #0 input is sampled in the Observed region rather than
  // in the Preponed one, so a stated zero is not the same as a stated nothing.
  sig.is_explicit_zero_skew =
      skew != nullptr && !sig.is_one_step_skew && sig.skew.ticks == 0;
  return sig;
}

// §14.3's clocking block as the run's ClockingManager keeps it, or nothing
// where the declaration names nothing the run could reach it by.
//
// §14.3 requires a name unless the block is the default or the global clocking,
// and §14.10 makes the event a block triggers "the event associated with the
// clocking block name", so an anonymous block has no name for a clockvar or an
// `@(cb)` to spell and there is nothing to register it under. A clocking event
// that is not a plain identifier names no variable the clock watcher could
// attach to, which is the other way a declaration arrives with nothing here to
// use.
std::optional<ClockingBlock> BuildClockingBlock(const ModuleItem* item,
                                                SimContext& ctx, Arena& arena) {
  if (item->name.empty() || item->clocking_event.empty()) return std::nullopt;
  const Expr* clock = item->clocking_event[0].signal;
  if (clock == nullptr || clock->kind != ExprKind::kIdentifier) {
    return std::nullopt;
  }
  ClockingBlock block;
  block.name = item->name;
  block.clock_signal = clock->text;
  block.clock_edge = item->clocking_event[0].edge;
  block.default_input_skew =
      ClockingSkewOf(item->default_input_skew_delay, ctx, arena);
  block.default_output_skew =
      ClockingSkewOf(item->default_output_skew_delay, ctx, arena);
  block.is_global = item->is_global_clocking;
  for (const auto& decl : item->clocking_signals) {
    block.signals.push_back(ClockingSignalOf(decl, item, ctx, arena));
  }
  return block;
}

}  // namespace

// §14.3: registers the module's clocking blocks with the run's manager, which
// is what gives the run the blocks at all. Three constructs read what is
// registered here: §14.13's sampled values read each input's direction and
// skew, §14.16's synchronous drive reads each output's skew, and §14.10's
// clocking block event reads the variable created under the block's name.
//
// The names are taken as the source wrote them. A block declared in a child
// instance would need the instance prefix on the block name, on its clock and
// on every signal, while the clockvar spellings that read them back -- the `cb`
// of `cb.sig <= ...` and of `always @(cb)` -- carry no prefix at all, so the
// two halves would have to agree on one before an instance's block could
// resolve. That is why this runs for a top module's blocks alone.
void Lowerer::LowerClockingBlocks(const RtlirModule* mod) {
  for (const ModuleItem* item : mod->clocking_blocks) {
    auto block = BuildClockingBlock(item, ctx_, arena_);
    if (!block.has_value()) continue;
    auto& mgr = ctx_.AcquireClockingManager();
    mgr.Register(*block);
    // §14.12: "the default clocking" and §14.14's global clocking are the two
    // the source can name without naming the block, so which block each is has
    // to be recorded beside the registration.
    if (item->is_default_clocking) mgr.SetDefaultClocking(item->name);
    if (item->is_global_clocking) mgr.SetGlobalClocking(item->name);

    // §14.10: "Upon processing its specified clocking event, a clocking block
    // shall trigger the event associated with the clocking block name." That
    // event is a variable here, because `always @(cb)` resolves `cb` through
    // SimContext::FindVariable and an event variable is what EventAwaiter
    // attaches a notify-driven watcher to. ClockingManager::NotifyBlockEvent
    // notifies it from the Observed region, which is where the clause puts it.
    auto* event_var = ctx_.CreateVariable(item->name, 1);
    if (event_var == nullptr) continue;
    event_var->is_event = true;
    mgr.SetBlockEventVar(item->name, event_var);
  }
}

// §14.3: arms the design's clocking blocks once every module has been lowered.
// ClockingManager::Attach watches each block's clock, and the variable it
// watches is created by the module that declares it, so nothing may be armed
// until the last of them exists.
void Lowerer::AttachDesignClocking() {
  auto* mgr = ctx_.GetClockingManager();
  if (mgr == nullptr) return;
  mgr->Attach(ctx_, ctx_.GetScheduler());
}

}  // namespace delta
