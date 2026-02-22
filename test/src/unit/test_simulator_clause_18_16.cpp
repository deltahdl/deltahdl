// §18.16: Random weighted case—randcase

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/exec_task.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/stmt_exec.h"
#include "simulation/stmt_result.h"
#include "simulation/variable.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string_view>

using namespace delta;

// Helper fixture providing scheduler, arena, diag, and sim context.
struct StmtFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, /*seed=*/42};
};

// Helper to create a simple identifier expression.
Expr *MakeIdent(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper to create an integer literal expression.
Expr *MakeIntLit(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper to create a blocking assignment statement: lhs = rhs_val.
Stmt *MakeBlockAssign(Arena &arena, std::string_view lhs_name,
                      uint64_t rhs_val) {
  auto *s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeIdent(arena, lhs_name);
  s->rhs = MakeIntLit(arena, rhs_val);
  return s;
}

// Driver coroutine that co_awaits an ExecTask and stores its result.
struct DriverResult {
  StmtResult value = StmtResult::kDone;
};

SimCoroutine DriverCoroutine(const Stmt *stmt, SimContext &ctx, Arena &arena,
                             DriverResult *out) {
  out->value = co_await ExecStmt(stmt, ctx, arena);
}

// Helper to run ExecStmt synchronously (for non-suspending statements).
// Creates a wrapper coroutine, resumes it, and returns the result.
StmtResult RunStmt(const Stmt *stmt, SimContext &ctx, Arena &arena) {
  DriverResult result;
  auto coro = DriverCoroutine(stmt, ctx, arena, &result);
  coro.Resume();
  return result.value;
}
namespace {

// =============================================================================
// 7. Randcase (StmtKind::kRandcase)
// =============================================================================
TEST(StmtExec, RandcaseSelectsBranch) {
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("r", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // randcase
  //   1 : r = 10;
  //   1 : r = 20;
  // endcase
  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 1), MakeBlockAssign(f.arena, "r", 10)});
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 1), MakeBlockAssign(f.arena, "r", 20)});

  RunStmt(stmt, f.ctx, f.arena);
  uint64_t val = result_var->value.ToUint64();
  EXPECT_TRUE(val == 10 || val == 20);
}

TEST(StmtExec, RandcaseAllZeroWeightsNoOp) {
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("rz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 0), MakeBlockAssign(f.arena, "rz", 10)});
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 0), MakeBlockAssign(f.arena, "rz", 20)});

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 0u);
}

TEST(StmtExec, RandcaseSingleBranchAlwaysSelected) {
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("rs", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 5), MakeBlockAssign(f.arena, "rs", 42)});

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

// =============================================================================
// 16. Randcase weighted selection
// =============================================================================
TEST(StmtExec, RandcaseRespectsWeights) {
  // Use a fixed seed; all branches should have weight > 0.
  StmtFixture f;
  auto *result_var = f.ctx.CreateVariable("rw", 32);

  // Run randcase many times and check distribution.
  // Weight 100 vs weight 0: should always pick first.
  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 100), MakeBlockAssign(f.arena, "rw", 1)});
  stmt->randcase_items.push_back(
      {MakeIntLit(f.arena, 0), MakeBlockAssign(f.arena, "rw", 2)});

  for (int i = 0; i < 10; ++i) {
    result_var->value = MakeLogic4VecVal(f.arena, 32, 0);
    RunStmt(stmt, f.ctx, f.arena);
    EXPECT_EQ(result_var->value.ToUint64(), 1u);
  }
}

} // namespace
