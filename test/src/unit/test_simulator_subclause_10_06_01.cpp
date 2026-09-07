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
  // After a deassign the held value persists until the variable is reassigned.
  // Besides an ordinary procedural assignment, a fresh procedural continuous
  // assignment is one of the ways that new value can be installed; here the
  // second assign must take effect and re-establish the forced state.
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
  // The held value also gives way to a nonblocking procedural assignment, which
  // reaches the variable through a different scheduling path than a blocking
  // one; once the deassign has cleared the forced state the nonblocking update
  // must land.
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

// §10.6.1: "The left-hand side of the assignment in the assign statement shall
// be a singular variable reference or a concatenation of variables." The
// concatenation is the second of the two forms the clause admits, and
// ProceduralAssignDeassignElaboration.AssignConcatenationLhs accepts
// `assign {a, b} = 2'b10;`, so the statement reaches the simulator and owes
// each element the bits its own width claims of the one right-hand value, the
// leftmost element taking the most significant ones: 8'h12 for a and 8'h34
// for b out of 16'h1234. The later `a = 8'd7;` is what reads the clause's own
// sentence back -- the assign "shall override all procedural assignments to a
// variable" -- so a reading 8'h12 says the override reached the element as well
// as the value did.
//
// The wrong answer was that nothing happened at all, and silently: the executor
// that force and assign share resolved its one target through
// ResolveLhsVariable, which answers null for a concatenation, so no element was
// written, none was marked, and the assignment after it landed. Both elements
// start at sentinels no expected value can be, so an assign that writes nothing
// cannot pass for one that wrote the right answer.
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

// §10.6.1: "The deassign procedural statement shall end an assign procedural
// continuous assignment to a variable. The value of the variable shall remain
// the same until the variable is assigned a new value through a procedural
// assignment or a procedural continuous assignment."
// ProceduralAssignDeassignElaboration.DeassignConcatenationLhs accepts
// `deassign {a, b};` after the same assign, so the deassign has to end the
// assignment on every element the assign made, and each element keeps the slice
// it was given. That is DeassignRetainsValue reached through a concatenation.
//
// The wrong answer was that both statements were no-ops: the deassign resolved
// its target the same way the assign did and cleared nothing, which is also why
// a fix to the assign alone would leave an assign no deassign could end.
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

// §10.6.1 names "a concatenation of variables" without bounding its nesting,
// and ProceduralAssignDeassignElaboration.AssignNestedConcatOfVariablesLhs
// accepts `assign {a, {b, c}} = 3'b101;` on that reading, so an inner
// concatenation is one more element of the outer one and distributes its own
// slice among its own elements the way §11.4.12 treats every concatenation
// lvalue. Out of 24'h123456 the outer's first element a takes 8'h12, the inner
// takes the remaining 16 bits and hands 8'h34 to b and 8'h56 to c.
//
// The wrong answer was that nothing happened at all. An arm that walked one
// level of elements and wrote each resolved variable is the other wrong answer
// this case names: the inner concatenation resolves to no variable, so b and c
// would stand at their sentinels while a alone took its slice.
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
