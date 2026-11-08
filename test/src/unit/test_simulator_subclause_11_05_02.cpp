#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ArrayAddressing, XZAddressReadReturnsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "result");
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

TEST(ArrayAddressing, OutOfBoundsAddressReadReturnsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    mem[1] = 8'h20;\n"
      "    result = mem[10];\n"
      "  end\n"
      "endmodule\n",
      f, "result");
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

TEST(ArrayAddressing, BitSelectWriteAfterArrayElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'h00;\n"
      "    arr[0][3] = 1'b1;\n"
      "    result = arr[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x08u);
}

TEST(ArrayAddressing, PartSelectWriteAfterArrayElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    arr[1] = 8'h00;\n"
      "    arr[1][7:4] = 4'hF;\n"
      "    result = arr[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xF0u);
}

TEST(ArrayAddressing, NonblockingBitSelectWriteAfterArrayElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    arr[2] = 8'h00;\n"
      "    arr[2][3] <= 1'b1;\n"
      "    #1;\n"
      "    result = arr[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x08u);
}

TEST(ArrayAddressing, BitSelectWriteAfterMultidimensionalArrayElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] twod [0:3][0:3];\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    twod[1][2] = 8'h00;\n"
      "    twod[1][2][3] = 1'b1;\n"
      "    result = twod[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x08u);
}

}  // namespace
