#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
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

// §10.6.2 makes the force's right-hand side a continuous assignment -- that a
// change of b or c forces a to the new value of b + f(c) is the clause's own
// example -- so a concatenation target is re-evaluated on a source change the
// same way ForceRhsReevaluatesOnVariableChange above says a singular one is.
// What is new here is that the recomputed value is one value for two targets:
// each element owns only the window §11.4.12 gives it, so a takes the top 12
// bits and b the bottom 4 of every recomputation, not just of the first. x + y
// is 16'h1234 when the force executes, giving a 12'h123 and b 4'h4; after x
// changes it is 16'h4678, giving a 12'h467 and b 4'h8. The widths are
// deliberately unequal, so an element handed an even share of the value would
// read 12'h046 rather than 12'h467, and one handed the whole recomputed value
// would read 12'h678.
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

// §10.6: the right-hand side of a force is re-evaluated when any variable it
// reads changes, a variable of another instance named by its path among them,
// and so is one reading a member of a structure. `u1.x` was watched as `u1`
// and `x`, neither a variable, so the force kept its first value.
TEST(ProceduralContinuousAssignSim, ForceFollowsAVariableItReadsByPath) {
  const char* src =
      "module sub; logic [7:0] x = 8'h01; endmodule\n"
      "module t;\n"
      "  sub u1();\n"
      "  struct packed { logic [7:0] f; } s;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    s.f = 8'h02;\n"
      "    force a = u1.x;\n"
      "    force b = s.f;\n"
      "    #1 u1.x = 8'h5a;\n"
      "    s.f = 8'h6b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x5au);
  EXPECT_EQ(RunAndGet(src, "b"), 0x6bu);
}

// §10.7 with §10.6: a force or a procedural assign evaluates its right-hand
// side in the context of its target's width, carrying into a wider variable
// and sign-extending into a select. Evaluated at the operands' own eight bits,
// a + b lost its carry, and 2'sb11 filled bus[7:4] with zeros above its two
// bits.
TEST(ProceduralContinuousAssignSim, ForceAndAssignTakeTheTargetsWidth) {
  const char* src =
      "module t;\n"
      "  logic [7:0] a = 8'hFF, b = 8'h01;\n"
      "  logic [15:0] w, v;\n"
      "  wire [7:0] bus;\n"
      "  logic [7:0] hi;\n"
      "  initial begin\n"
      "    force w = a + b;\n"
      "    assign v = a + b;\n"
      "    force bus[7:4] = 2'sb11;\n"
      "    #1 hi = bus;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "w"), 0x0100u);
  EXPECT_EQ(RunAndGet(src, "v"), 0x0100u);
  EXPECT_EQ(RunAndGet(src, "hi") >> 4, 0xFu);
}

}  // namespace
