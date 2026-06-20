#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "helpers_switch_network.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ForceReleaseSim, VarLvalueForce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; force x = 8'hFF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(ForceReleaseExec, ForceOverridesValue) {
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

TEST(ForceReleaseExec, ForceNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = nullptr;
  stmt->rhs = MakeInt(f.arena, 5);

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ForceReleaseExec, ReleaseClearsForce) {
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

TEST(ForceReleaseExec, ReleaseUnknownVarNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = MakeId(f.arena, "nonexistent");

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ForceReleaseExec, ForcePreventsNormalAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("fv", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* force_stmt = f.arena.Create<Stmt>();
  force_stmt->kind = StmtKind::kForce;
  force_stmt->lhs = MakeId(f.arena, "fv");
  force_stmt->rhs = MakeInt(f.arena, 50);
  RunStmt(force_stmt, f.ctx, f.arena);

  auto* assign_stmt = MakeBlockAssign(f.arena, "fv", 100);
  RunStmt(assign_stmt, f.ctx, f.arena);

  EXPECT_TRUE(var->is_forced);

  EXPECT_EQ(var->forced_value.ToUint64(), 50u);
}

TEST(ForceReleaseExec, ForceReleaseThenAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("fra", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* force_stmt = f.arena.Create<Stmt>();
  force_stmt->kind = StmtKind::kForce;
  force_stmt->lhs = MakeId(f.arena, "fra");
  force_stmt->rhs = MakeInt(f.arena, 50);
  RunStmt(force_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 50u);
  EXPECT_TRUE(var->is_forced);

  auto* release_stmt = f.arena.Create<Stmt>();
  release_stmt->kind = StmtKind::kRelease;
  release_stmt->lhs = MakeId(f.arena, "fra");
  RunStmt(release_stmt, f.ctx, f.arena);
  EXPECT_FALSE(var->is_forced);

  auto* assign_stmt = MakeBlockAssign(f.arena, "fra", 75);
  RunStmt(assign_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 75u);
}

TEST(ForceReleaseExec, ReleaseNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kRelease;
  stmt->lhs = nullptr;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ForceReleaseSim, ForcePreventsNonblockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x <= 8'd100;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ReforceUpdatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    force x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 99u);
}

TEST(ForceReleaseSim, ForceOverridesBlockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    force x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 99u);
  EXPECT_TRUE(x->is_forced);
}

TEST(ForceReleaseSim, ReleaseVariableHoldsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    release x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForceOverridesAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    assign x = 8'd10;\n"
      "    force x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 99u);
}

TEST(ForceReleaseSim, ForcePreventsBlockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x = 8'd100;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForceExpressionRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    force b = a | 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xFFu);
}

TEST(ForceReleaseSim, ReleaseReestablishesAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    assign x = 8'd10;\n"
      "    force x = 8'd99;\n"
      "    release x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 10u);
}

TEST(ForceReleaseSim, ReleaseReestablishesContinuousAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] x;\n"
      "  assign x = src;\n"
      "  initial begin\n"
      "    src = 8'd10;\n"
      "    #1;\n"
      "    force x = 8'd99;\n"
      "    #1;\n"
      "    release x;\n"
      "    src = 8'd42;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 42u);
}

TEST(ForceReleaseSim, ForceOnNetOverridesContinuousDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  assign w = 8'd10;\n"
      "  initial begin\n"
      "    #1;\n"
      "    force w = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 99u);
}

TEST(ForceReleaseSim, ReleaseOnNetUsesDriverValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] w;\n"
      "  assign w = src;\n"
      "  initial begin\n"
      "    src = 8'd10;\n"
      "    #1;\n"
      "    force w = 8'd99;\n"
      "    #1;\n"
      "    release w;\n"
      "    src = 8'd55;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_FALSE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 55u);
}

// A force on a net overrides every kind of driver until the net is released,
// not just continuous assignments. Here a primitive AND gate drives w to 1,
// yet the force holds w at 0 while it is in effect.
TEST(ForceReleaseSim, ForceOverridesGateOutputDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  wire w;\n"
      "  and g(w, a, b);\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    #1;\n"
      "    force w = 1'b0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 0u);
}

// Releasing a net makes it take the value its drivers determine right away.
// After release the AND gate (1 & 1) drives w back to 1, displacing the
// forced 0.
TEST(ForceReleaseSim, ReleaseNetReturnsToGateOutputValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  wire w;\n"
      "  and g(w, a, b);\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    #1;\n"
      "    force w = 1'b0;\n"
      "    #1;\n"
      "    release w;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_FALSE(w->is_forced);
  EXPECT_EQ(w->value.ToUint64(), 1u);
}

}  // namespace
