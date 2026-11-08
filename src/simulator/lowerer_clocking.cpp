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

ClockingDir ClockingDirOf(Direction dir) {
  if (dir == Direction::kOutput) return ClockingDir::kOutput;
  if (dir == Direction::kInout) return ClockingDir::kInout;
  return ClockingDir::kInput;
}

struct ClockingLowerScope {
  const std::string& inst_prefix;
  SimContext& ctx;
  Arena& arena;
};

bool IsOneStepSkew(const Expr* delay) {
  return delay != nullptr && delay->text == "1step";
}

SimTime ClockingSkewOf(const Expr* delay, const ClockingLowerScope& scope) {
  if (delay == nullptr || IsOneStepSkew(delay)) return SimTime{0};
  return SimTime{
      DelayValueToTicks(EvalExpr(delay, scope.ctx, scope.arena), scope.ctx)};
}

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
  sig.signal_name = decl.name;
  if (decl.hier_expr != nullptr) {
    std::string path;
    BuildLhsName(decl.hier_expr, path);
    if (!path.empty()) {
      sig.target_path = *scope.arena.Create<std::string>(std::move(path));
    } else {
      sig.target_expr = decl.hier_expr;
    }
  }
  sig.direction = ClockingDirOf(decl.direction);
  const Expr* skew = SkewExprOf(decl, item, sig.direction);
  sig.skew = ClockingSkewOf(skew, scope);
  sig.is_one_step_skew = IsOneStepSkew(skew);
  sig.is_explicit_zero_skew =
      skew != nullptr && !sig.is_one_step_skew && sig.skew.ticks == 0;
  if (sig.direction != ClockingDir::kOutput)
    sig.sample_edge = SampleEdgeOf(decl, item);
  if (sig.direction != ClockingDir::kInput)
    sig.drive_edge = DriveEdgeOf(decl, item, sig.direction);
  return sig;
}

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

void Lowerer::LowerClockingBlocks(const RtlirModule* mod) {
  for (size_t index = 0; index < mod->clocking_blocks.size(); ++index) {
    const ModuleItem* item = mod->clocking_blocks[index];
    const RtlirGenBlockClocking* gen = FindGenBlockClocking(mod, index);
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
    if (item->is_default_clocking) {
      mgr.SetDefaultClocking(block->name);
      mgr.SetScopeDefaultClocking(inst_prefix_, block->name);
    }
    if (item->is_global_clocking) mgr.SetGlobalClocking(block->name);

    auto* event_var = ctx_.CreateVariable(block->name, 1);
    if (event_var == nullptr) continue;
    event_var->is_event = true;
    mgr.SetBlockEventVar(block->name, event_var);
    AliasGenBlockClockingBlock(gen, *block, ctx_, arena_);
  }
}

void Lowerer::AttachDesignClocking() {
  auto* mgr = ctx_.GetClockingManager();
  if (mgr == nullptr) return;
  mgr->Attach(ctx_, ctx_.GetScheduler());
}

}  // namespace delta
