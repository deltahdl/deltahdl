// §12.4.2: unique-if, unique0-if, and priority-if

#include <gtest/gtest.h>
#include <cstdint>
#include <string_view>
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
Expr* MakeIdent(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper to create an integer literal expression.
Expr* MakeIntLit(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper to create a blocking assignment statement: lhs = rhs_val.
Stmt* MakeBlockAssign(Arena& arena, std::string_view lhs_name,
                      uint64_t rhs_val) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeIdent(arena, lhs_name);
  s->rhs = MakeIntLit(arena, rhs_val);
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
// 11. Unique if / Priority if
// =============================================================================
TEST(StmtExec, UniqueIfMatchingBranch) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("ui", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // unique if (1) ui = 10; else ui = 20;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->qualifier = CaseQualifier::kUnique;
  stmt->condition = MakeIntLit(f.arena, 1);
  stmt->then_branch = MakeBlockAssign(f.arena, "ui", 10);
  stmt->else_branch = MakeBlockAssign(f.arena, "ui", 20);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 10u);
}

TEST(StmtExec, PriorityIfFirstMatchTaken) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("pi", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // priority if (1) pi = 30;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->qualifier = CaseQualifier::kPriority;
  stmt->condition = MakeIntLit(f.arena, 1);
  stmt->then_branch = MakeBlockAssign(f.arena, "pi", 30);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 30u);
}

TEST(StmtExec, PriorityIfNoMatchNoElseWarning) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("piw", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // priority if (0) piw = 30;
  // No else branch => should emit warning but not crash.
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kIf;
  stmt->qualifier = CaseQualifier::kPriority;
  stmt->condition = MakeIntLit(f.arena, 0);
  stmt->then_branch = MakeBlockAssign(f.arena, "piw", 30);

  RunStmt(stmt, f.ctx, f.arena);
  // Value should remain 0 since condition is false and no else.
  EXPECT_EQ(result_var->value.ToUint64(), 0u);
  // DiagEngine should have emitted a warning.
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

}  // namespace
