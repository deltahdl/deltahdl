#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_gen_block_clocking.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec_internal.h"
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

// Where a clocking block is being lowered: the instance prefix its names belong
// to and the context and arena a constant skew is folded against. Bundled
// because the three travel together through every step below.
struct ClockingLowerScope {
  const std::string& inst_prefix;
  SimContext& ctx;
  Arena& arena;
};

// §14.4: an input skew left unwritten is 1step, which names the value the
// signal held in the time step before the clocking event rather than a delay
// measured after it. The parser writes that skew as a literal spelled `1step`
// (Parser::ParseClockingSkew), and the mark travels with the signal because
// ClockingManager reads a recorded previous-step value for it and an elapsed
// skew for every other.
bool IsOneStepSkew(const Expr* delay) {
  return delay != nullptr && delay->text == "1step";
}

// §14.4's clocking skew as a number of time units. The clause requires a skew
// to be a constant expression, which elaboration has already checked
// (Elaborator::ValidateClockingBlock), so it is folded here against the context
// the design is being lowered into. A 1step skew measures no delay at all and
// is carried by the mark above instead.
SimTime ClockingSkewOf(const Expr* delay, const ClockingLowerScope& scope) {
  if (delay == nullptr || IsOneStepSkew(delay)) return SimTime{0};
  // §14.4: a skew is a delay, in the declaring scope's time unit or the unit
  // it writes, `#2ns`, so it is scaled to ticks as any delay is.
  return SimTime{
      DelayValueToTicks(EvalExpr(delay, scope.ctx, scope.arena), scope.ctx)};
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

// §14.3's clocking_skew written as an edge, `input negedge d`, for the
// sampling side of an input or inout item and the driving side of an output
// or inout one, read as SkewExprOf reads the delay: the item's own skew where
// it wrote one, the block's default otherwise. An output-only item keeps its
// skew in the first pair of fields, an inout in the second.
Edge SampleEdgeOf(const ClockingSignalDecl& decl, const ModuleItem* item) {
  if (decl.skew_edge != Edge::kNone || decl.skew_delay != nullptr)
    return decl.skew_edge;
  return item->default_input_skew_edge;
}

Edge DriveEdgeOf(const ClockingSignalDecl& decl, const ModuleItem* item,
                 ClockingDir dir) {
  Edge own = dir == ClockingDir::kOutput ? decl.skew_edge : decl.out_skew_edge;
  const Expr* own_delay =
      dir == ClockingDir::kOutput ? decl.skew_delay : decl.out_skew_delay;
  if (own != Edge::kNone || own_delay != nullptr) return own;
  return item->default_output_skew_edge;
}

ClockingSignal ClockingSignalOf(const ClockingSignalDecl& decl,
                                const ModuleItem* item,
                                const ClockingLowerScope& scope) {
  ClockingSignal sig;
  // §14.3 names a signal by the bare name of the module the block stands in,
  // which is how ClockingBlock keeps it; ClockingBlock::inst_prefix is what
  // joins it to the instance's own variable.
  sig.signal_name = decl.name;
  // §14.3: `output d = top.d` drives and samples the signal the expression
  // names rather than a signal of the clockvar's own name.
  if (decl.hier_expr != nullptr) {
    std::string path;
    BuildLhsName(decl.hier_expr, path);
    if (!path.empty()) {
      sig.target_path = *scope.arena.Create<std::string>(std::move(path));
    } else {
      // §14.5 (printed pages 357-358): an expression that is no name, a slice
      // or a concatenation, is sampled and driven as the expression it is.
      sig.target_expr = decl.hier_expr;
    }
  }
  sig.direction = ClockingDirOf(decl.direction);
  const Expr* skew = SkewExprOf(decl, item, sig.direction);
  sig.skew = ClockingSkewOf(skew, scope);
  sig.is_one_step_skew = IsOneStepSkew(skew);
  // §14.4: an explicit #0 input is sampled in the Observed region rather than
  // in the Preponed one, so a stated zero is not the same as a stated nothing.
  sig.is_explicit_zero_skew =
      skew != nullptr && !sig.is_one_step_skew && sig.skew.ticks == 0;
  if (sig.direction != ClockingDir::kOutput)
    sig.sample_edge = SampleEdgeOf(decl, item);
  if (sig.direction != ClockingDir::kInput)
    sig.drive_edge = DriveEdgeOf(decl, item, sig.direction);
  return sig;
}

// §14.3's clocking block as the run's ClockingManager keeps it, or nothing
// where the declaration names nothing the run could reach it by.
//
// §14.3 requires a name unless the block is the default or the global clocking,
// and §14.10 makes the event a block triggers the one its name carries, so an
// anonymous block has no name for a clockvar or an `@(cb)` to spell and there
// is nothing to register it under. A clocking event that is neither a name nor
// a hierarchical name names no variable the clock watcher could attach to,
// which is the other way a declaration arrives with nothing here to use.
//
// §14.3 (printed page 354) with §23.6: the event may name its clock by a
// hierarchical name, `@(posedge top.clk)`, which is kept as it is spelled and
// resolved from the block's instance when the watcher attaches
// (ClockingManager::Attach). Dropped here, the block never fired and a process
// waiting in `@(cb)` waited for ever.
//
// §14.3 (printed page 355) makes the identifier optional for the default and
// the global clocking, which the source reaches through `##` and
// `$global_clock` rather than by name, so such a block is registered under a
// name no source can spell. Dropped for want of one, an unnamed `default
// clocking @(posedge clk)` was no default and every `##` ran on at once.
std::string_view RegisteredBlockName(const ModuleItem* item) {
  if (!item->name.empty()) return item->name;
  if (item->is_default_clocking) return "$default_clocking";
  if (item->is_global_clocking) return "$global_clocking";
  return {};
}

std::optional<ClockingBlock> BuildClockingBlock(
    const ModuleItem* item, const ClockingLowerScope& scope) {
  std::string_view own_name = RegisteredBlockName(item);
  if (own_name.empty() || item->clocking_event.empty()) return std::nullopt;
  const Expr* clock = item->clocking_event[0].signal;
  if (clock == nullptr || (clock->kind != ExprKind::kIdentifier &&
                           clock->kind != ExprKind::kMemberAccess)) {
    return std::nullopt;
  }
  ClockingBlock block;
  // §14.3 names a block within its module, so two instances of one module
  // declare two blocks of one name; the instance prefix is what registers them
  // apart, and ClockingManager::FindInScope is what reaches each from the bare
  // name a reference in that instance spells. Both strings are arena-persisted
  // because the manager keys on a string_view.
  block.name = *scope.arena.Create<std::string>(scope.inst_prefix +
                                                std::string(own_name));
  block.inst_prefix = *scope.arena.Create<std::string>(scope.inst_prefix);
  if (clock->kind == ExprKind::kIdentifier && clock->scope_prefix.empty()) {
    block.clock_signal = clock->text;
  } else {
    std::string path;
    BuildLhsName(clock, path);
    block.clock_signal = *scope.arena.Create<std::string>(std::move(path));
  }
  block.clock_edge = item->clocking_event[0].edge;
  block.clock_iff = item->clocking_event[0].iff_condition;
  block.default_input_skew =
      ClockingSkewOf(item->default_input_skew_delay, scope);
  block.default_output_skew =
      ClockingSkewOf(item->default_output_skew_delay, scope);
  block.is_global = item->is_global_clocking;
  for (const auto& decl : item->clocking_signals) {
    block.signals.push_back(ClockingSignalOf(decl, item, scope));
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
// §23.9: a block is registered under the instance prefix of the module
// declaring it, because §14.3 names it within its module and two instances of
// one module therefore declare two blocks of one name. The clock and the
// signals stay as the source wrote them, ClockingBlock::inst_prefix joining
// them to the instance's own variables, and a reference spelling the bare name
// -- the `cb` of `cb.sig <= ...`, of `@(cb.sig)` and of `always @(cb)` --
// reaches the running instance's block through ClockingManager::FindInScope.
void Lowerer::LowerClockingBlocks(const RtlirModule* mod) {
  for (size_t index = 0; index < mod->clocking_blocks.size(); ++index) {
    const ModuleItem* item = mod->clocking_blocks[index];
    // §14.3 with §27.4: a block declared in a generate block is that block
    // instance's, registered under its prefix and named through its path.
    const RtlirGenBlockClocking* gen = FindGenBlockClocking(mod, index);
    // §14.12 (printed page 362): `default clocking busB;` declares no block
    // but makes the one of that name, declared in the same scope, the default,
    // so what is recorded is that block's registered name. Dropped for its want
    // of a clocking event, it made no block the default.
    if (item->is_default_clocking && item->clocking_event.empty() &&
        !item->name.empty()) {
      auto& mgr = ctx_.AcquireClockingManager();
      std::string_view named = *arena_.Create<std::string>(
          inst_prefix_ + GenBlockClockingPrefix(gen) + std::string(item->name));
      mgr.SetDefaultClocking(named);
      mgr.SetScopeDefaultClocking(inst_prefix_, named);
      continue;
    }
    ClockingLowerScope scope{inst_prefix_, ctx_, arena_};
    auto block = BuildClockingBlock(item, scope);
    if (!block.has_value()) continue;
    PlaceClockingBlockInGenBlock(gen, *block, ctx_, arena_);
    auto& mgr = ctx_.AcquireClockingManager();
    mgr.Register(*block);
    // §14.12's default clocking and §14.14's global clocking are the two
    // the source can name without naming the block, so which block each is has
    // to be recorded beside the registration.
    if (item->is_default_clocking) {
      mgr.SetDefaultClocking(block->name);
      mgr.SetScopeDefaultClocking(inst_prefix_, block->name);
    }
    if (item->is_global_clocking) mgr.SetGlobalClocking(block->name);

    // §14.10: when its clocking event is processed, a clocking block triggers
    // the event its name carries. That event is a variable here, because
    // `always @(cb)` resolves `cb` through SimContext::FindVariable and an
    // event variable is what EventAwaiter attaches a notify-driven watcher to.
    // ClockingManager::NotifyBlockEvent notifies it from the Observed region,
    // which is where the clause puts it. The variable carries the instance
    // prefix for the reason the block does, and SimContext::FindVariable is
    // what joins a bare `cb` written inside the instance to it.
    auto* event_var = ctx_.CreateVariable(block->name, 1);
    if (event_var == nullptr) continue;
    event_var->is_event = true;
    mgr.SetBlockEventVar(block->name, event_var);
    AliasGenBlockClockingBlock(gen, *block, ctx_, arena_);
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
