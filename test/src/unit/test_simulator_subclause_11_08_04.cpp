#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

Logic4Vec RunVar(const std::string& src, const char* name, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return {};
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr);
  return var ? var->value : Logic4Vec{};
}

TEST(SignedXZ, AssignWidenSignBitXFillsWithXEndToEnd) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  initial begin\n"
      "    b = 4'bx111;\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n",
      "a", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);
}

TEST(SignedXZ, AssignWidenSignBitZFillsWithZEndToEnd) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  initial begin\n"
      "    b = 4'bz111;\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n",
      "a", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0x00u);
}

TEST(SignedXZ, TernaryWidenSignBitXFillsWithXEndToEnd) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [7:0] w;\n"
      "  logic signed [7:0] r;\n"
      "  initial begin\n"
      "    s = 4'bx111;\n"
      "    w = 0;\n"
      "    r = 1'b1 ? s : w;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);
}

TEST(SignedXZ, TernaryWidenSignBitZFillsWithZEndToEnd) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [7:0] w;\n"
      "  logic signed [7:0] r;\n"
      "  initial begin\n"
      "    s = 4'bz111;\n"
      "    w = 0;\n"
      "    r = 1'b1 ? s : w;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0x00u);
}

TEST(SignedXZ, KnownSignBitWidensWithoutUnknownFill) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  initial begin\n"
      "    b = -1;\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n",
      "a", f);
  EXPECT_EQ(v.words[0].bval & 0xFFu, 0x00u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);
}

TEST(SignedXZ, AssignWidenSignBitXFillsThroughNonblocking) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  initial begin\n"
      "    b = 4'bx111;\n"
      "    a <= b;\n"
      "  end\n"
      "endmodule\n",
      "a", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);
}

TEST(SignedXZ, AssignWidenSignBitXFillsThroughContinuousAssign) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] b;\n"
      "  logic signed [7:0] a;\n"
      "  assign a = b;\n"
      "  initial b = 4'bx111;\n"
      "endmodule\n",
      "a", f);
  EXPECT_EQ(v.words[0].bval & 0xF0u, 0xF0u);
  EXPECT_EQ(v.words[0].aval & 0xF0u, 0xF0u);
}

TEST(SignedXZ, WideSignBitXFillsAcrossMultipleWords) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [39:0] b;\n"
      "  logic signed [95:0] a;\n"
      "  initial begin\n"
      "    b = 40'bx;\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n",
      "a", f);
  EXPECT_EQ(v.words[1].bval & 0xFFFFFFFFu, 0xFFFFFFFFu);
  EXPECT_EQ(v.words[1].aval & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

TEST(SignedXZ, SignedAdditionWithXBitYieldsAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b, r;\n"
      "  initial begin\n"
      "    a = 4'b010x;\n"
      "    b = 4'd1;\n"
      "    r = a + b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0xFu);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0xFu);
}

TEST(SignedXZ, SignedMultiplicationWithZBitYieldsAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b, r;\n"
      "  initial begin\n"
      "    a = 4'b010z;\n"
      "    b = 4'd2;\n"
      "    r = a * b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0xFu);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0xFu);
}

TEST(SignedXZ, SignedPowerWithXBitYieldsAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b, r;\n"
      "  initial begin\n"
      "    a = 4'b011x;\n"
      "    b = 4'd2;\n"
      "    r = a ** b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0xFu);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0xFu);
}

TEST(SignedXZ, UnaryMinusOnXSignedYieldsAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, r;\n"
      "  initial begin\n"
      "    a = 4'b010x;\n"
      "    r = -a;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0xFu);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0xFu);
}

TEST(SignedXZ, RelationalWithXYieldsSingleXBit) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b010x;\n"
      "    b = 4'd1;\n"
      "    r = a < b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.width, 1u);
  EXPECT_NE(v.words[0].bval & 0x1u, 0u);
}

TEST(SignedXZ, KnownSignedNonlogicalOpNotAllX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, b, r;\n"
      "  initial begin\n"
      "    a = 4'd5;\n"
      "    b = 4'd2;\n"
      "    r = a - b;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0x0u);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0x3u);
}

TEST(SignedXZ, BitwiseAndWithZeroStaysDefinedDespiteX) {
  SimFixture f;
  auto v = RunVar(
      "module t;\n"
      "  logic signed [3:0] a, r;\n"
      "  initial begin\n"
      "    a = 4'b010x;\n"
      "    r = a & 4'b0000;\n"
      "  end\n"
      "endmodule\n",
      "r", f);
  EXPECT_EQ(v.words[0].bval & 0xFu, 0x0u);
  EXPECT_EQ(v.words[0].aval & 0xFu, 0x0u);
}

}  // namespace
