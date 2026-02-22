// §10.6.1: The assign and deassign procedural statements

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
// 2. Assign / Deassign (StmtKind::kAssign, kDeassign)
// =============================================================================
TEST(StmtExec, ProceduralAssignSetsValue) {
  StmtFixture f;
  auto *var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kAssign;
  stmt->lhs = MakeIdent(f.arena, "a");
  stmt->rhs = MakeIntLit(f.arena, 77);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_TRUE(var->is_forced);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(StmtExec, DeassignReleasesProceduralAssign) {
  StmtFixture f;
  auto *var = f.ctx.CreateVariable("b", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 50);
  var->is_forced = true;
  var->forced_value = MakeLogic4VecVal(f.arena, 32, 50);

  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->lhs = MakeIdent(f.arena, "b");

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);
}

TEST(StmtExec, DeassignNullLhsNoOp) {
  StmtFixture f;
  auto *stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->lhs = nullptr;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// =============================================================================
// 20. Assign then deassign then blocking assign
// =============================================================================
TEST(StmtExec, AssignDeassignBlockingAssign) {
  StmtFixture f;
  auto *var = f.ctx.CreateVariable("adb", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // assign adb = 33;
  auto *assign_stmt = f.arena.Create<Stmt>();
  assign_stmt->kind = StmtKind::kAssign;
  assign_stmt->lhs = MakeIdent(f.arena, "adb");
  assign_stmt->rhs = MakeIntLit(f.arena, 33);
  RunStmt(assign_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 33u);
  EXPECT_TRUE(var->is_forced);

  // deassign adb;
  auto *deassign_stmt = f.arena.Create<Stmt>();
  deassign_stmt->kind = StmtKind::kDeassign;
  deassign_stmt->lhs = MakeIdent(f.arena, "adb");
  RunStmt(deassign_stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);

  // adb = 44;
  auto *blocking_stmt = MakeBlockAssign(f.arena, "adb", 44);
  RunStmt(blocking_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

}  // namespace
