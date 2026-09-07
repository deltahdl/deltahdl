#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ProceduralContinuousAssignSim, AssignRhsReevaluatesOnVariableChange) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    assign q = a + b;\n"
      "    #1;\n"
      "    a = 8'd100;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 120u);
}

TEST(ProceduralContinuousAssignSim, ForceRhsReevaluatesOnVariableChange) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] b, c, a;\n"
      "  initial begin\n"
      "    b = 8'd1;\n"
      "    c = 8'd2;\n"
      "    force a = b + c;\n"
      "    #1;\n"
      "    b = 8'd50;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 52u);
}

// The head's rule treats the assign/force RHS as a continuous assignment,
// reevaluating it whenever *any* RHS variable changes. The LRM's own example
// is `force a = b + f(c)`, where a variable (c) appears only as a function-call
// argument -- it must still be a reevaluation source.
TEST(ProceduralContinuousAssignSim,
     ForceReevaluatesOnFunctionCallArgumentChange) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] b, c, a;\n"
      "  function logic [7:0] dbl(input logic [7:0] x);\n"
      "    return x + x;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    b = 8'd1;\n"
      "    c = 8'd2;\n"
      "    force a = b + dbl(c);\n"
      "    #1;\n"
      "    c = 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  // b + dbl(c) = 1 + (10+10) = 21; unchanged (5) if the func-call argument
  // were not collected as a reevaluation source.
  EXPECT_EQ(a->value.ToUint64(), 21u);
}

TEST(ProceduralContinuousAssignSim, ForceReevaluatesForEachRhsVariableChange) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] b, c, a;\n"
      "  initial begin\n"
      "    b = 8'd1;\n"
      "    c = 8'd2;\n"
      "    force a = b + c;\n"
      "    #1; b = 8'd10;\n"
      "    #1; c = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 30u);
}

// §10.6.2 makes the force's right-hand side a continuous assignment -- "if b or
// c changes, a will be forced to the new value of the expression b + f(c)" is
// the clause's own example -- so a concatenation target is re-evaluated on a
// source change the same way ForceRhsReevaluatesOnVariableChange above says a
// singular one is. What is new here is that the recomputed value is one value
// for two targets: each element owns only the window §11.4.12 gives it, so a
// takes the top 12 bits and b the bottom 4 of every recomputation, not just of
// the first. x + y is 16'h1234 when the force executes, giving a 12'h123 and b
// 4'h4; after x changes it is 16'h4678, giving a 12'h467 and b 4'h8. The widths
// are deliberately unequal, so an element handed an even share of the value
// would read 12'h046 rather than 12'h467, and one handed the whole recomputed
// value would read 12'h678.
//
// The wrong answer was that the force did nothing at all: it resolved its one
// target through ResolveLhsVariable, which answers null for a concatenation, so
// no value was deposited and no watcher was installed on x or y, leaving a and
// b at the sentinels they were initialised to.
TEST(ProceduralContinuousAssignSim,
     ForceOfAConcatenationReevaluatesEachElementsSlice) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x, y;\n"
      "  logic [11:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    a = 12'hAAA;\n"
      "    b = 4'hF;\n"
      "    x = 16'h1000;\n"
      "    y = 16'h0234;\n"
      "    force {a, b} = x + y;\n"
      "    #1;\n"
      "    x = 16'h4444;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x467u);
  EXPECT_EQ(b->value.ToUint64(), 0x8u);
}

}  // namespace
