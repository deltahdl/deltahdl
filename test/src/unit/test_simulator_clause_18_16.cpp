// §18.16: Random weighted case—randcase

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"
#include "builders_ast.h"
#include "helpers_stmt_exec.h"

using namespace delta;

// Helper to create a blocking assignment statement: lhs = rhs_val.

// Driver coroutine that co_awaits an ExecTask and stores its result.

// Helper to run ExecStmt synchronously (for non-suspending statements).
// Creates a wrapper coroutine, resumes it, and returns the result.
namespace {

// =============================================================================
// 7. Randcase (StmtKind::kRandcase)
// =============================================================================
TEST(StmtExec, RandcaseSelectsBranch) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("r", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // randcase
  //   1 : r = 10;
  //   1 : r = 20;
  // endcase
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 1), MakeBlockAssign(f.arena, "r", 10)});
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 1), MakeBlockAssign(f.arena, "r", 20)});

  RunStmt(stmt, f.ctx, f.arena);
  uint64_t val = result_var->value.ToUint64();
  EXPECT_TRUE(val == 10 || val == 20);
}

TEST(StmtExec, RandcaseAllZeroWeightsNoOp) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rz", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 0), MakeBlockAssign(f.arena, "rz", 10)});
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 0), MakeBlockAssign(f.arena, "rz", 20)});

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 0u);
}

TEST(StmtExec, RandcaseSingleBranchAlwaysSelected) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rs", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 5), MakeBlockAssign(f.arena, "rs", 42)});

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

// =============================================================================
// 16. Randcase weighted selection
// =============================================================================
TEST(StmtExec, RandcaseRespectsWeights) {
  // Use a fixed seed; all branches should have weight > 0.
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("rw", 32);

  // Run randcase many times and check distribution.
  // Weight 100 vs weight 0: should always pick first.
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRandcase;
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 100), MakeBlockAssign(f.arena, "rw", 1)});
  stmt->randcase_items.push_back(
      {MakeInt(f.arena, 0), MakeBlockAssign(f.arena, "rw", 2)});

  for (int i = 0; i < 10; ++i) {
    result_var->value = MakeLogic4VecVal(f.arena, 32, 0);
    RunStmt(stmt, f.ctx, f.arena);
    EXPECT_EQ(result_var->value.ToUint64(), 1u);
  }
}

}  // namespace
