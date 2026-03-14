#include <gtest/gtest.h>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"

namespace {

// --- §15.5.3: Nonblocking trigger sets triggered state ---

TEST(IpcSync, NonblockingTriggerSetsTriggeredState) {
  SyncFixture f;

  auto* ev = f.ctx.CreateVariable("my_event", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* trigger_stmt = f.arena.Create<Stmt>();
  trigger_stmt->kind = StmtKind::kNbEventTrigger;
  trigger_stmt->expr = f.arena.Create<Expr>();
  trigger_stmt->expr->kind = ExprKind::kIdentifier;
  trigger_stmt->expr->text = "my_event";

  auto result = RunStmt(trigger_stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);

  // Triggered state is set after NBA region executes.
  f.scheduler.Run();
  EXPECT_TRUE(f.ctx.IsEventTriggered("my_event"));
}

// --- §15.5.3 tests ---

TEST(IpcSync, TriggeredMethodReturnsOneWhenTriggered) {
  SimFixture f;
  auto* ev = f.ctx.CreateVariable("ev", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);
  f.ctx.SetEventTriggered("ev");

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "ev");
  access->rhs = MakeId(f.arena, "triggered");

  auto result = EvalExpr(access, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(IpcSync, TriggeredMethodReturnsZeroByDefault) {
  SimFixture f;
  auto* ev = f.ctx.CreateVariable("ev", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "ev");
  access->rhs = MakeId(f.arena, "triggered");

  auto result = EvalExpr(access, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(IpcSync, WaitTriggeredProceedsWhenAlreadyTriggered) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "    wait(ev.triggered);\n"
      "    result = 55;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(IpcSync, WaitTriggeredUnblocksInFork) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event blast;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    fork\n"
      "      -> blast;\n"
      "      begin wait(blast.triggered); result = 42; end\n"
      "    join\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IpcSync, WaitTriggeredUnblocksWhenTriggerAfterWait) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait(ev.triggered);\n"
      "    result = 77;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 -> ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(IpcSync, NullEventTriggeredReturnsFalse) {
  SimFixture f;
  auto* ev = f.ctx.CreateVariable("ev", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "ev");
  access->rhs = MakeId(f.arena, "triggered");

  auto result = EvalExpr(access, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(IpcSync, WaitTriggeredWithBodyStatement) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    #5 -> ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  initial\n"
      "    wait(ev.triggered) x = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

}  // namespace
