#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §11.5 para 1: a complete-form reference to a variable uses all of the
// variable's bits as the operand. Built from a real §6.8 declaration and driven
// end-to-end so the whole 32-bit value flows through to the target.
TEST(Eval, VariableReferenceUsesAllBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] y;\n"
      "  initial begin a = 32'hDEADBEEF; y = a; end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(v, 0xDEADBEEFu);
}

// §11.5 para 1: for a scalar variable the operand is its whole (single-bit)
// value.
TEST(Eval, SingleBitVariableUsesAllBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic a;\n"
      "  logic y;\n"
      "  initial begin a = 1'b1; y = a; end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(v, 1u);
}

// §11.5 para 4: a concatenation (§11.4.12) is an operand whose bits are the
// ordered bits of its elements. Elements come from real §6.8 declarations and
// the concatenation is evaluated through the full pipeline.
TEST(Eval, ConcatenationAsOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] y;\n"
      "  initial begin hi = 4'hA; lo = 4'h5; y = {hi, lo}; end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(v, 0xA5u);
}

// §11.5 para 4: a nested concatenation is likewise an operand.
TEST(Eval, NestedConcatenationAsOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [3:0] a, b, c;\n"
      "  logic [11:0] y;\n"
      "  initial begin a = 4'h1; b = 4'h2; c = 4'h3; y = {a, {b, c}}; end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(v, 0x123u);
}

TEST(Eval, FunctionCallAsOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  int result;\n"
      "  initial result = add(10, 20);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(Eval, ParameterReferenceAsOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int WIDTH = 42;\n"
      "  int x;\n"
      "  initial x = WIDTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(Eval, BitSelectAsOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic b;\n"
      "  initial begin a = 8'hA5; b = a[7]; end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 1u);
}

TEST(Eval, PartSelectAsOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial begin a = 8'hA5; b = a[3:0]; end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 0x5u);
}

TEST(Eval, UnpackedArrayElementAsOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  int arr[4];\n"
      "  int x;\n"
      "  initial begin arr[2] = 42; x = arr[2]; end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(v, 42u);
}

TEST(Eval, NetReferenceUsesAllBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  wire [31:0] w;\n"
      "  assign w = 32'hDEADBEEF;\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(v, 0xDEADBEEFu);
}

}  // namespace
