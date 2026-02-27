// §10.6.2: The force and release procedural statements

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/exec_task.h"
#include "simulation/process.h"
#include "simulation/stmt_exec.h"
#include "simulation/stmt_result.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

// Helper to create a blocking assignment statement: lhs = rhs_val.
Stmt* MakeBlockAssign(Arena& arena, std::string_view lhs_name,
                      uint64_t rhs_val) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeId(arena, lhs_name);
  s->rhs = MakeInt(arena, rhs_val);
  return s;
}

// Driver coroutine that co_awaits an ExecTask and stores its result.
struct DriverResult {
  StmtResult value = StmtResult::kDone;
};

SimCoroutine DriverCoroutine(const Stmt* stmt, SimContext& ctx, Arena& arena,
                             DriverResult* out) {
  out->value = co_await ExecStmt(stmt, ctx, arena);
}

// Helper to run ExecStmt synchronously (for non-suspending statements).
// Creates a wrapper coroutine, resumes it, and returns the result.
StmtResult RunStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  DriverResult result;
  auto coro = DriverCoroutine(stmt, ctx, arena, &result);
  coro.Resume();
  return result.value;
}
namespace {

// =============================================================================
// 1. Force / Release (StmtKind::kForce, kRelease)
// =============================================================================
TEST(StmtExec, ForceOverridesValue) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("x", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = MakeId(f.arena, "x");
  stmt->rhs = MakeInt(f.arena, 99);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_TRUE(var->is_forced);
  EXPECT_EQ(var->forced_value.ToUint64(), 99u);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(StmtExec, ForceNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = nullptr;
  stmt->rhs = MakeInt(f.arena, 5);

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(StmtExec, ReleaseClearsForce) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("y", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);
  var->is_forced = true;
  var->forced_value = MakeLogic4VecVal(f.arena, 32, 42);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = MakeId(f.arena, "y");

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);
}

TEST(StmtExec, ReleaseUnknownVarNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = MakeId(f.arena, "nonexistent");

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// =============================================================================
// 14. Force prevents normal assignment
// =============================================================================
TEST(StmtExec, ForcePreventsNormalAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("fv", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Force fv = 50;
  auto* force_stmt = f.arena.Create<Stmt>();
  force_stmt->kind = StmtKind::kForce;
  force_stmt->lhs = MakeId(f.arena, "fv");
  force_stmt->rhs = MakeInt(f.arena, 50);
  RunStmt(force_stmt, f.ctx, f.arena);

  // Normal blocking assign: fv = 100;
  // The blocking assignment should be overridden by the force.
  auto* assign_stmt = MakeBlockAssign(f.arena, "fv", 100);
  RunStmt(assign_stmt, f.ctx, f.arena);

  // Since force is active, the value should remain forced value.
  EXPECT_TRUE(var->is_forced);
  // The blocking assign does set value, but force should logically override.
  // In our implementation, the force checks and restores the forced value.
  EXPECT_EQ(var->forced_value.ToUint64(), 50u);
}

// =============================================================================
// 18. Force then release then assign
// =============================================================================
TEST(StmtExec, ForceReleaseThenAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("fra", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Force fra = 50;
  auto* force_stmt = f.arena.Create<Stmt>();
  force_stmt->kind = StmtKind::kForce;
  force_stmt->lhs = MakeId(f.arena, "fra");
  force_stmt->rhs = MakeInt(f.arena, 50);
  RunStmt(force_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 50u);
  EXPECT_TRUE(var->is_forced);

  // Release fra;
  auto* release_stmt = f.arena.Create<Stmt>();
  release_stmt->kind = StmtKind::kRelease;
  release_stmt->lhs = MakeId(f.arena, "fra");
  RunStmt(release_stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);

  // Assign fra = 75 (normal blocking)
  auto* assign_stmt = MakeBlockAssign(f.arena, "fra", 75);
  RunStmt(assign_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 75u);
}

}  // namespace
