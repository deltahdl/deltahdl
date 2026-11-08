#include <gtest/gtest.h>

#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ProceduralAssignDeassignSim, DeassignNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kDeassign;
  stmt->lhs = nullptr;

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

TEST(ProceduralContinuousAssignSim, AssignOverridesProceduralAssign) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 42u);
  EXPECT_TRUE(q->is_forced);
}

TEST(ProceduralContinuousAssignSim, DeassignRetainsValue) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd50;\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_FALSE(q->is_forced);

  EXPECT_EQ(q->value.ToUint64(), 50u);
}

TEST(ProceduralContinuousAssignSim, ReAssignReplacesFirst) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd10;\n"
      "    assign q = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 20u);
  EXPECT_TRUE(q->is_forced);
}

TEST(ProceduralContinuousAssignSim, AssignExpressionRhs) {
  SimFixture f;
  auto* c = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd15;\n"
      "    b = 8'd27;\n"
      "    assign c = a + b;\n"
      "  end\n"
      "endmodule\n",
      f, "c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 42u);
}

TEST(ProceduralContinuousAssignSim, AssignBlocksBlockingAssignFullSim) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd42;\n"
      "    q = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 42u);
}

TEST(ProceduralContinuousAssignSim, AssignBlocksNonblockingAssign) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd42;\n"
      "    q <= 8'd99;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
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

TEST(ProceduralContinuousAssignSim,
     DeassignRetainsValueThenBlockingOverwrites) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd50;\n"
      "    deassign q;\n"
      "    q = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 77u);
}

TEST(ProceduralContinuousAssignSim,
     DeassignRetainsValueThenContinuousOverwrites) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd50;\n"
      "    deassign q;\n"
      "    assign q = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 99u);
  EXPECT_TRUE(q->is_forced);
}

TEST(ProceduralContinuousAssignSim,
     DeassignRetainsValueThenNonblockingOverwrites) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    assign q = 8'd50;\n"
      "    deassign q;\n"
      "    q <= 8'd88;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 88u);
}

TEST(ProceduralContinuousAssignSim, DFlipFlopClearPresetPattern) {
  SimFixture f;
  auto* q = RunAndFindVar(
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
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0u);
  EXPECT_TRUE(q->is_forced);
}

TEST(ProceduralContinuousAssignSim, ReAssignClearsOldRhsWatcher) {
  SimFixture f;
  auto* q = RunAndFindVar(
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
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 2u);
}

TEST(ProceduralContinuousAssignSim,
     AssignOfAConcatenationDistributesToItsElements) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hA1;\n"
      "    b = 8'hB2;\n"
      "    assign {a, b} = 16'h1234;\n"
      "    a = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x12u);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
  EXPECT_TRUE(a->is_forced);
  EXPECT_TRUE(b->is_forced);
}

TEST(ProceduralContinuousAssignSim,
     DeassignOfAConcatenationEndsItOnEachElement) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hA1;\n"
      "    b = 8'hB2;\n"
      "    assign {a, b} = 16'h1234;\n"
      "    deassign {a, b};\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_FALSE(a->is_forced);
  EXPECT_FALSE(b->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 0x12u);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
}

TEST(ProceduralContinuousAssignSim,
     AssignOfANestedConcatenationReachesTheInnerElements) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'hA1;\n"
      "    b = 8'hB2;\n"
      "    c = 8'hC3;\n"
      "    assign {a, {b, c}} = 24'h123456;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x12u);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
  EXPECT_EQ(c->value.ToUint64(), 0x56u);
  EXPECT_TRUE(c->is_forced);
}

}  // namespace
