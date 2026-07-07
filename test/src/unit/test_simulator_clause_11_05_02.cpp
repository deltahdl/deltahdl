#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §11.5.2 — the declared address bounds of the memory determine the effect of
// the address expression; an address with one or more x or z bits is invalid
// and the read yields x (as described in 7.4.5). Built from real declaration
// and procedural-read syntax so the memory's declared bounds drive the outcome.
TEST(ArrayAddressing, XZAddressReadReturnsX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [7:0] result;\n"
      "  logic [1:0] idx;\n"
      "  initial begin\n"
      "    mem[1] = 8'h20;\n"
      "    idx = 2'bx0;\n"
      "    result = mem[idx];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
}

TEST(MemorySimulation, WordWriteAndReadByAddress) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mema [0:255];\n"
      "  int result;\n"
      "  int addr;\n"
      "  initial begin\n"
      "    mema[5] = 8'hA5;\n"
      "    addr = 5;\n"
      "    result = mema[addr];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xA5u);
}

TEST(MultidimensionalArraySimulation, TwoDimElementAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:3][0:3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[1][2] = 8'hAB;\n"
      "    result = mem[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

// §11.5.2 — access to a multidimensional array supplies one integer expression
// per addressed dimension. For the three-dimensional form the LRM spells out
// (threed_array[addr][addr][addr]), addressing all three dimensions selects the
// whole element word and reads it back intact.
TEST(MultidimensionalArraySimulation, ThreeDimElementAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] threed [0:3][0:3][0:7];\n"
      "  int result;\n"
      "  initial begin\n"
      "    threed[1][2][3] = 8'hC7;\n"
      "    result = threed[1][2][3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xC7u);
}

// §11.5.2 — the LRM also contrasts an array whose element is a whole vector
// with one whose element is a single bit (three_array). Supplying an address
// for every dimension of a single-bit-element array selects exactly that one
// bit.
TEST(MultidimensionalArraySimulation, SingleBitElementArrayAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic bits [0:3][0:3][0:7];\n"
      "  logic result;\n"
      "  initial begin\n"
      "    bits[1][2][3] = 1'b1;\n"
      "    result = bits[1][2][3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(ArrayAddressing, MemoryIndirection) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:7];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[3] = 8'd1;\n"
      "    mem[1] = 8'hCD;\n"
      "    result = mem[mem[3]];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xCDu);
}

TEST(ArrayAddressing, ComputedIndexExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:7];\n"
      "  int result;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    mem[5] = 8'hEF;\n"
      "    a = 2;\n"
      "    b = 3;\n"
      "    result = mem[a + b];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xEFu);
}

// §11.5.2 — the address expression may be any integer expression, which
// includes a reference to a parameter. Built from real parameter-declaration
// syntax so elaboration folds the constant that then drives the element
// selection.
TEST(ArrayAddressing, ParameterIndexReadsElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter P = 5;\n"
      "  logic [7:0] mem [0:7];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[5] = 8'h3C;\n"
      "    result = mem[P];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x3Cu);
}

// §11.5.2 — a localparam address operand takes the same "any integer
// expression" path; it resolves to its constant value and addresses that word.
TEST(ArrayAddressing, LocalparamIndexReadsElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam L = 6;\n"
      "  logic [7:0] mem [0:7];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[6] = 8'h9A;\n"
      "    result = mem[L];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x9Au);
}

// §11.5.2 — as with bit-selects, the memory's declared bounds govern the
// address: an out-of-range address is invalid and a read of a 4-state memory
// yields x (per 7.4.5). Driven through the full pipeline from real syntax
// rather than a hand-registered array so the [0:3] declaration is what makes 10
// invalid.
TEST(ArrayAddressing, OutOfBoundsAddressReadReturnsX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    mem[1] = 8'h20;\n"
      "    result = mem[10];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
}

TEST(ArrayAddressing, BitSelectAfterArrayElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic result;\n"
      "  initial begin\n"
      "    arr[2] = 8'b01000000;\n"
      "    result = arr[2][6];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(ArrayAddressing, PartSelectAfterArrayElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] twod [0:3][0:3];\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    twod[1][2] = 8'hA5;\n"
      "    result = twod[1][2][3:0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x5u);
}

// §11.5.2 — once every array dimension has been addressed, the selected word
// may be bit-selected with a run-time (variable) index, as in
// twod_array[1][3][sel].
TEST(ArrayAddressing, VariableBitSelectAfterArrayElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] twod [0:3][0:3];\n"
      "  logic result;\n"
      "  int sel;\n"
      "  initial begin\n"
      "    twod[1][2] = 8'b00100000;\n"
      "    sel = 5;\n"
      "    result = twod[1][2][sel];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

}  // namespace
