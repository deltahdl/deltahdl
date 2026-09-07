#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(AdditionBitLength, SameWidthLhsDropsCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] sumA;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumA = a + b;\n"
      "  end\n"
      "endmodule\n",
      f, "sumA");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

TEST(AdditionBitLength, WiderLhsPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] sumB;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumB = a + b;\n"
      "  end\n"
      "endmodule\n",
      f, "sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

TEST(AdditionBitLength, ContinuousAssignWiderLhsPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  wire  [16:0] sumB;\n"
      "  assign sumB = a + b;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "  end\n"
      "endmodule\n",
      f, "sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

TEST(AdditionBitLength, NonblockingAssignWiderLhsPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] sumB;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumB <= a + b;\n"
      "  end\n"
      "endmodule\n",
      f, "sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

TEST(AdditionBitLength, SingleBitOperandsCarryIntoTwoBitLhs) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic a, b;\n"
      "  logic [1:0] sumB;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    sumB = a + b;\n"
      "  end\n"
      "endmodule\n",
      f, "sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x2u);
}

// Operand-kind coverage: the addends are sized 16-bit literals rather than
// variables. The assignment's 17-bit target must still set the width the '+'
// is evaluated at, so the carry-out lands in bit 16 instead of being truncated
// away at the operands' own 16-bit width.
TEST(AdditionBitLength, LiteralOperandsWiderLhsPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [16:0] sumB;\n"
      "  initial sumB = 16'hFFFF + 16'h0001;\n"
      "endmodule\n",
      f, "sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

// Syntactic-position coverage: a declaration initializer is an assignment, so
// the initialized variable's 17-bit width is the context the '+' is evaluated
// in -- the carry-out must survive here just as it does for the procedural,
// continuous, and nonblocking forms above. Self-determined evaluation at the
// operands' 16-bit width would instead zero the result.
TEST(AdditionBitLength, DeclarationInitializerWiderLhsPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [16:0] sumB = 16'hFFFF + 16'h0001;\n"
      "endmodule\n",
      f, "sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

// The positions above are all outside a subroutine. A subroutine body runs on
// the statement executor in eval_function_body.cpp rather than the one in
// statement_assign_core.cpp, and that executor evaluated its right-hand side
// with no assignment context at all, so the same sum written inside a function
// added at the operands' sixteen bits and handed 0 to a seventeen-bit target.
// §11.6's example is the one the cases above use, so it is the one used here.
TEST(AdditionBitLength, FunctionBodyWiderLhsPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] sumB;\n"
      "  function void add();\n"
      "    sumB = a + b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    add();\n"
      "  end\n"
      "endmodule\n",
      f, "sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

// A task called with parentheses runs its body on the ordinary statement
// executor rather than the subroutine one: SetupTaskCall claims a kTaskDecl
// and ExecInlineTaskCall walks the body through ExecStmt, where a void
// function of the same shape is declined there and reaches ExecFunctionBody.
// So this is the rule read through a task call rather than a second reading of
// the subroutine executor, and the function case above is what claims that.
TEST(AdditionBitLength, TaskBodyWiderLhsPreservesCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] sumB;\n"
      "  task add();\n"
      "    sumB = a + b;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    add();\n"
      "  end\n"
      "endmodule\n",
      f, "sumB");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

// §11.6 sizes the addition by "the bit length of the largest operand, including
// the left-hand side", so a left-hand side no wider than the operands adds no
// bit and the carry is still dropped. This is the half that says the context is
// the target's own width rather than some width large enough to hold anything:
// a body that widened every sum to a word would report 0x10000 here too.
TEST(AdditionBitLength, FunctionBodySameWidthLhsStillDropsCarry) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] sumA;\n"
      "  function void add();\n"
      "    sumA = a + b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    add();\n"
      "  end\n"
      "endmodule\n",
      f, "sumA");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

}  // namespace
