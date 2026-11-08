#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ConcatenationSim, ConcatenationSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = {4'hA, 4'h5};\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(ConcatenationSim, MultipleConcatenationSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = {2{4'hF}};\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(ConcatenationSim, StreamingConcatenationSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "    x = {>> {a, b}};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(ConcatenationSim, EmptyUnpackedArrayConcatenationSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    q = {};\n"
      "    x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ConcatenationSim, ConstantConcatenationSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter P = {8'hAB, 8'hCD};\n"
      "  logic [15:0] x;\n"
      "  initial x = P;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(ConcatenationSim, ConstantMultipleConcatenationSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter P = {4{4'hF}};\n"
      "  logic [15:0] x;\n"
      "  initial x = P;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
}

TEST(ConcatenationSim, ConcatenationOfExpressionSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, x;\n"
      "  initial begin\n"
      "    a = 8'h20;\n"
      "    b = 8'h15;\n"
      "    x = {a + b};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x35u);
}

TEST(ConcatenationSim, StreamingConcatByteSliceSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "    x = {<< byte {a, b}};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDABu);
}

TEST(ConcatenationSim, StreamingConcatOperatorSliceSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam int W = 4;\n"
      "  logic [31:0] x;\n"
      "  initial x = {<< W*2 {32'h11223344}};\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x44332211u);
}

TEST(ConcatenationSim, MultipleConcatenationParameterCountSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter N = 4;\n"
      "  parameter P = {N{4'hF}};\n"
      "  logic [15:0] x;\n"
      "  initial x = P;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
}

}  // namespace
