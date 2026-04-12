#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ProceduralAssignDeassignSim, ProceduralAssignSetsValue) {
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

TEST(ProceduralAssignDeassignSim, DeassignReleasesProceduralAssign) {
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

TEST(ProceduralAssignDeassignSim, DeassignNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->lhs = nullptr;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ProceduralAssignDeassignSim, AssignDeassignBlockingAssign) {
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

TEST(ProceduralContinuousAssignSim, AssignOverridesProceduralAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 42u);
  EXPECT_TRUE(q->is_forced);
}

TEST(ProceduralContinuousAssignSim, DeassignThenProceduralAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd10;\n"
      "    deassign q;\n"
      "    q = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_FALSE(q->is_forced);
  EXPECT_EQ(q->value.ToUint64(), 77u);
}

TEST(ProceduralContinuousAssignSim, DeassignRetainsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd50;\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_FALSE(q->is_forced);

  EXPECT_EQ(q->value.ToUint64(), 50u);
}

TEST(ProceduralContinuousAssignSim, ReAssignReplacesFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd10;\n"
      "    assign q = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 20u);
  EXPECT_TRUE(q->is_forced);
}

TEST(ProceduralContinuousAssignSim, AssignExpressionRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd15;\n"
      "    b = 8'd27;\n"
      "    assign c = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 42u);
}

TEST(ProceduralAssignDeassignSim, AssignBlocksBlockingAssign) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("q", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* assign_stmt = f.arena.Create<Stmt>();
  assign_stmt->kind = StmtKind::kAssign;
  assign_stmt->lhs = MakeId(f.arena, "q");
  assign_stmt->rhs = MakeInt(f.arena, 42);
  RunStmt(assign_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);

  auto* blocking_stmt = MakeBlockAssign(f.arena, "q", 99);
  RunStmt(blocking_stmt, f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ProceduralContinuousAssignSim, AssignBlocksBlockingAssignFullSim) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd42;\n"
      "    q = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 42u);
}

TEST(ProceduralContinuousAssignSim, AssignBlocksNonblockingAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd42;\n"
      "    q <= 8'd99;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 42u);
}

TEST(ProceduralAssignDeassignSim, AssignNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kAssign;
  stmt->lhs = nullptr;
  stmt->rhs = MakeInt(f.arena, 1);

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ProceduralAssignDeassignSim, DeassignUnknownVarNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->lhs = MakeId(f.arena, "nonexistent");

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ProceduralContinuousAssignSim, DeassignRetainsValueThenBlockingOverwrites) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd50;\n"
      "    deassign q;\n"
      "    q = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 77u);
}

TEST(ProceduralContinuousAssignSim, DFlipFlopClearPresetPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic q;\n"
      "  logic clear, preset;\n"
      "  initial begin\n"
      "    clear = 0;\n"
      "    preset = 1;\n"
      "  end\n"
      "  always @(clear or preset)\n"
      "    if (!clear)\n"
      "      assign q = 0;\n"
      "    else if (!preset)\n"
      "      assign q = 1;\n"
      "    else\n"
      "      deassign q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0u);
  EXPECT_TRUE(q->is_forced);
}

TEST(ProceduralContinuousAssignSim, ReAssignClearsOldRhsWatcher) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    assign q = a;\n"
      "    assign q = b;\n"
      "    #1;\n"
      "    a = 8'd100;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 2u);
}

}  // namespace
