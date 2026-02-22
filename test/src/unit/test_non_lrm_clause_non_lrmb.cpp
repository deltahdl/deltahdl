// §non_lrm

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/compiled_sim.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

// =============================================================================
// CompiledProcess
// =============================================================================
TEST(CompiledSim, ValidCompiledProcess) {
  bool executed = false;
  CompiledProcess proc(1,
                       [&executed](SimContext& /*ctx*/) { executed = true; });
  EXPECT_EQ(proc.Id(), 1u);
  EXPECT_TRUE(proc.IsValid());
}

TEST(CompiledSim, InvalidCompiledProcess) {
  CompiledProcess proc(0, nullptr);
  EXPECT_FALSE(proc.IsValid());
}

// =============================================================================
// ProcessCompiler::IsCompilable
// =============================================================================
TEST(CompiledSim, PureCombinationalIsCompilable) {
  Arena arena;
  auto* assign = arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;

  auto* block = arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  EXPECT_TRUE(ProcessCompiler::IsCompilable(block));
}

TEST(CompiledSim, TimingControlNotCompilable) {
  Arena arena;
  auto* delay = arena.Create<Stmt>();
  delay->kind = StmtKind::kDelay;

  auto* block = arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(delay);

  EXPECT_FALSE(ProcessCompiler::IsCompilable(block));
}

TEST(CompiledSim, NestedTimingControlDetected) {
  Arena arena;
  auto* event_ctrl = arena.Create<Stmt>();
  event_ctrl->kind = StmtKind::kEventControl;

  auto* inner = arena.Create<Stmt>();
  inner->kind = StmtKind::kBlock;
  inner->stmts.push_back(event_ctrl);

  auto* if_stmt = arena.Create<Stmt>();
  if_stmt->kind = StmtKind::kIf;
  if_stmt->then_branch = inner;

  auto* outer = arena.Create<Stmt>();
  outer->kind = StmtKind::kBlock;
  outer->stmts.push_back(if_stmt);

  EXPECT_FALSE(ProcessCompiler::IsCompilable(outer));
}

TEST(CompiledSim, NullBodyNotCompilable) {
  EXPECT_FALSE(ProcessCompiler::IsCompilable(nullptr));
}

TEST(CompiledSim, CompileReturnsValidForCombinational) {
  Arena arena;
  auto* assign = arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;

  auto* block = arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(42, block);
  EXPECT_TRUE(compiled.IsValid());
  EXPECT_EQ(compiled.Id(), 42u);
}

}  // namespace
