#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ContinuousAssignSim, ContAssignExecutes) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [31:0] y;\n"
      "  assign y = 99;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ContinuousAssignSim, DrivesScalarNet) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ContinuousAssignSim, DrivesScalarVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic v;\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ContinuousAssignSim, DrivesVectorVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] v;\n"
      "  assign v = 16'hBEEF;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEEFu);
}

TEST(ContinuousAssignSim, AssignmentReevaluatesOnRhsChange) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  wire  [7:0] y;\n"
      "  assign y = a + b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    #1;\n"
      "    a = 8'd40;\n"
      "    b = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 42u);
}

// §10.3 makes a continuous assignment drive its left-hand side "whenever a
// change occurs in an operand in the right-hand side expression", and puts no
// condition on the shape of that operand. The case above reads two whole
// variables; this one reads a single bit of one, which is the operand form
// whose collected name -- BuildSelectPrefix's `a[1]` -- resolves to no
// simulation object, since `logic [3:0] a` is one Variable named `a`.
//
// The second write clears the bit the assignment reads while leaving the
// variable's other bits alone, so an assignment that never re-evaluated leaves
// y at 1. This states the defect without an instance array, so it stays red if
// a fix reaches only the array expansion.
TEST(ContinuousAssignSim, RhsBitSelectOfAPackedVectorTracksLaterChanges) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  wire y;\n"
      "  assign y = a[1];\n"
      "  initial begin\n"
      "    a = 4'b0010;\n"
      "    #1;\n"
      "    a = 4'b0000;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
}

}  // namespace
