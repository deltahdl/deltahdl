#include <cstdint>
#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StmtExec, ProceduralAssignSetsValue) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kAssign;
  stmt->lhs = MakeId(f.arena, "a");
  stmt->rhs = MakeInt(f.arena, 77);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_TRUE(var->is_forced);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(StmtExec, DeassignReleasesProceduralAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("b", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 50);
  var->is_forced = true;
  var->forced_value = MakeLogic4VecVal(f.arena, 32, 50);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->lhs = MakeId(f.arena, "b");

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);
}

TEST(StmtExec, DeassignNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->lhs = nullptr;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(StmtExec, AssignDeassignBlockingAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("adb", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* assign_stmt = f.arena.Create<Stmt>();
  assign_stmt->kind = StmtKind::kAssign;
  assign_stmt->lhs = MakeId(f.arena, "adb");
  assign_stmt->rhs = MakeInt(f.arena, 33);
  RunStmt(assign_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 33u);
  EXPECT_TRUE(var->is_forced);

  auto* deassign_stmt = f.arena.Create<Stmt>();
  deassign_stmt->kind = StmtKind::kDeassign;
  deassign_stmt->lhs = MakeId(f.arena, "adb");
  RunStmt(deassign_stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);

  auto* blocking_stmt = MakeBlockAssign(f.arena, "adb", 44);
  RunStmt(blocking_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

}  // namespace
