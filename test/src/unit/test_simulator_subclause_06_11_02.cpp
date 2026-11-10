#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(TwoStateAndFourState, UnsignedWideningZeroExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [3:0] src;\n"
      "  bit [7:0] dst;\n"
      "  initial begin\n"
      "    src = 4'hA;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0x0Au);
}

TEST(TwoStateAndFourState, SignedWideningSignExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = -2;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFEu);
}

TEST(TwoStateAndFourState, NarrowingTruncatesMSBs) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] src;\n"
      "  bit [3:0] dst;\n"
      "  initial begin\n"
      "    src = 8'hAB;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(TwoStateAndFourState, FourToTwoStateZeroesOnlyXzBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  bit [7:0] dst;\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, FourStateVariableHoldsXAndZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  initial a = 4'b1x0z;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1x0z");
}

TEST(TwoStateAndFourState, IntegerKeepsXzThatIntZeroes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  int two_state;\n"
      "  integer four_state;\n"
      "  initial begin\n"
      "    src = 8'bxxxxxxxx;\n"
      "    two_state = src;\n"
      "    four_state = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* two = f.ctx.FindVariable("two_state");
  auto* four = f.ctx.FindVariable("four_state");
  ASSERT_NE(two, nullptr);
  ASSERT_NE(four, nullptr);
  EXPECT_TRUE(two->value.IsKnown());
  EXPECT_EQ(two->value.ToUint64(), 0u);
  EXPECT_FALSE(four->value.IsKnown());
}

TEST(TwoStateAndFourState, PositiveSignedWideningFillsZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'sd5;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0x00000005u);
}

TEST(TwoStateAndFourState, LogicAndRegSimulateIdentically) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  reg [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hCA;\n"
      "    b = 8'hCA;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), vb->value.ToUint64());
  EXPECT_EQ(va->value.width, vb->value.width);
}

TEST(TwoStateAndFourState, MultiWordSignedWideningSignExtends) {
  SimFixture f;
  auto* dst = RunAndFindVar(
      "module t;\n"
      "  bit signed [31:0]  src;\n"
      "  bit signed [127:0] dst;\n"
      "  initial begin\n"
      "    src = 32'sh80000000;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.width, 128u);
  ASSERT_EQ(dst->value.nwords, 2u);

  EXPECT_EQ(dst->value.words[0].aval, 0xFFFFFFFF80000000ull);
  EXPECT_EQ(dst->value.words[1].aval, 0xFFFFFFFFFFFFFFFFull);
}

TEST(TwoStateAndFourState, MultiWordNarrowingTruncatesMSBs) {
  SimFixture f;
  auto* dst = RunAndFindVar(
      "module t;\n"
      "  bit [127:0] src;\n"
      "  bit [31:0]  dst;\n"
      "  initial begin\n"
      "    src = 128'hAAAAAAAA_BBBBBBBB_CCCCCCCC_DDDDDDDD;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.width, 32u);
  EXPECT_EQ(dst->value.ToUint64(), 0xDDDDDDDDu);
}

TEST(TwoStateAndFourState, MultiWordFourToTwoStateZeroesXz) {
  SimFixture f;
  auto* dst = RunAndFindVar(
      "module t;\n"
      "  logic [127:0] src;\n"
      "  bit   [127:0] dst;\n"
      "  initial begin\n"
      "    src = {64'hxxxxxxxxxxxxxxxx, 64'hCAFEBABEDEADBEEF};\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.width, 128u);
  ASSERT_EQ(dst->value.nwords, 2u);
  EXPECT_TRUE(dst->value.IsKnown());
  EXPECT_EQ(dst->value.words[0].aval, 0xCAFEBABEDEADBEEFull);
  EXPECT_EQ(dst->value.words[1].aval, 0ull);
}

TEST(TwoStateAndFourState, TwoStateInitializerZeroesXz) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] a = 8'b1010_x10z;\n"
      "  bit       b = 1'bx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_TRUE(va->value.IsKnown());
  EXPECT_EQ(va->value.ToUint64(), 0xA4u);
  EXPECT_TRUE(vb->value.IsKnown());
  EXPECT_EQ(vb->value.ToUint64(), 0u);
}

TEST(TwoStateAndFourState, FourStateInitializerKeepsXz) {
  SimFixture f;
  auto* va = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a = 8'b1010_x10z;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(va, nullptr);
  EXPECT_FALSE(va->value.IsKnown());
  EXPECT_EQ(va->value.ToString(), "1010x10z");
}

TEST(TwoStateAndFourState, RegHoldsXAndZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  reg [3:0] a;\n"
      "  initial a = 4'b1x0z;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1x0z");
}

TEST(TwoStateAndFourState, TimeHoldsXAndZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  time ts;\n"
      "  initial ts = 64'b1x0z;\n"
      "endmodule\n",
      f, "ts");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_FALSE(var->value.IsKnown());
}

TEST(TwoStateAndFourState, ByteConversionZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  byte dst;\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, ShortintConversionZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] src;\n"
      "  shortint dst;\n"
      "  initial begin\n"
      "    src = 16'b0000_0000_1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0x00A4u);
}

TEST(TwoStateAndFourState, LongintConversionZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] src;\n"
      "  longint dst;\n"
      "  initial begin\n"
      "    src = 64'b1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, UnsignedByteWideningZeroExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte unsigned src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0x000000FFu);
}

TEST(TwoStateAndFourState, FunctionBodyZeroesXzIntoATwoStateTarget) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  bit [7:0] dst;\n"
      "  function void copy();\n"
      "    dst = src;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    copy();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, FunctionBodyTwoStateLocalZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void copy();\n"
      "    bit [7:0] tmp;\n"
      "    tmp = src;\n"
      "    dst = tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    copy();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, FunctionBodyFourStateLocalKeepsXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void copy();\n"
      "    logic [7:0] tmp;\n"
      "    tmp = src;\n"
      "    dst = tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    copy();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1010x10z");
}

TEST(TwoStateAndFourState, FunctionBodyLocalOfATypedefNameKeepsXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef logic [7:0] octet;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void copy();\n"
      "    octet tmp;\n"
      "    tmp = src;\n"
      "    dst = tmp;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    copy();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1010x10z");
}

TEST(TwoStateAndFourState, TwoStateFormalZeroesXzAtTheCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void take(input bit [7:0] p);\n"
      "    dst = p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    take(src);\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, FourStateFormalKeepsXzAtTheCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function void take(input logic [7:0] p);\n"
      "    dst = p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    take(src);\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1010x10z");
}

TEST(TwoStateAndFourState, TwoStateFunctionReturnZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function bit [7:0] pass();\n"
      "    return src;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    dst = pass();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, TwoStateFunctionNameAssignZeroesXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] dst;\n"
      "  function bit [7:0] pass();\n"
      "    pass = src;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    dst = pass();\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, TwoStateUnpackedElementZeroesXzAtEitherRank) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] c [0:1];\n"
      "  bit [7:0] d [0:1][0:1];\n"
      "  initial begin\n"
      "    c[0] = 8'hxx;\n"
      "    d[0][0] = 8'hxx;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* vc = f.ctx.FindVariable("c[0]");
  auto* vd = f.ctx.FindVariable("d[0][0]");
  ASSERT_NE(vc, nullptr);
  ASSERT_NE(vd, nullptr);
  EXPECT_EQ(vc->value.ToString(), "00000000");
  EXPECT_EQ(vd->value.ToString(), vc->value.ToString());
}

TEST(TwoStateAndFourState, TwoStateUnpackedElementZeroesHighImpedance) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] c [0:1];\n"
      "  initial c[1] = 8'hzz;\n"
      "endmodule\n",
      f, "c[1]");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0u);
}

TEST(TwoStateAndFourState, FourStateUnpackedElementKeepsXz) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] e [0:1];\n"
      "  initial e[0] = 8'b1010_x10z;\n"
      "endmodule\n",
      f, "e[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1010x10z");
}

TEST(TwoStateAndFourState, TwoStateBodyLocalDropsItsInitializersUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  int result;\n"
      "  function automatic void probe();\n"
      "    int v = seed;\n"
      "    result = $isunknown(v);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seed = 8'b1x0z0000;\n"
      "    probe();\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(TwoStateAndFourState, TwoStateBodyLocalAssignedAfterDeclarationDropsThem) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  int result;\n"
      "  function void probe();\n"
      "    int v;\n"
      "    v = seed;\n"
      "    result = $isunknown(v);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seed = 8'b1x0z0000;\n"
      "    probe();\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(TwoStateAndFourState, TwoStateBodyLocalKeepsTheKnownBitsOfItsInitializer) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  int result;\n"
      "  function automatic void probe();\n"
      "    int v = seed;\n"
      "    result = v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seed = 8'b1010_x10z;\n"
      "    probe();\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, TwoStateArrayPositionalInitDropsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] c [0:1] = '{8'hxx, 8'h00};\n"
      "endmodule\n",
      f, "c[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

TEST(TwoStateAndFourState, TwoStateArrayReplicatedInitDropsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] c [0:1] = '{2{8'hxx}};\n"
      "endmodule\n",
      f, "c[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

TEST(TwoStateAndFourState, TwoStateArrayDefaultKeyedInitDropsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] c [0:1] = '{default: 8'hxx};\n"
      "endmodule\n",
      f, "c[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

TEST(TwoStateAndFourState, FourStateArrayPositionalInitKeepsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d [0:1] = '{8'hxx, 8'h00};\n"
      "endmodule\n",
      f, "d[0]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

TEST(TwoStateAndFourState, TwoStateArrayInitLeavesItsSourceVariableAlone) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] s = 8'hxx;\n"
      "  bit [7:0] c [0:1] = '{s, 8'h00};\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

TEST(TwoStateAndFourState, NegativeInitializerFillsALongintAndATime) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  longint lo = -1, lo2; time t = -1; longint neg;\n"
                 "  int i = -5;\n"
                 "  initial begin\n"
                 "    lo2 = i;\n"
                 "    neg = -(64'd1 << 32);\n"
                 "    $display(\"lo=%0d lo2=%0d t=%0d neg=%0d\", lo, lo2, "
                 "t, neg);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "lo=-1 lo2=-5 t=18446744073709551615 neg=-4294967296\n");
}

TEST(TwoStateAndFourState, SignednessDefaultsDecideTheReadOfAnInitializer) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  byte by = 200; shortint sh = 16'hFFFF;\n"
                 "  int i = 32'hFFFFFFFF; longint lo = -1; integer in = -1;\n"
                 "  bit [7:0] b = -1; logic [7:0] l = -1;\n"
                 "  int unsigned ui = -1; time t = -1;\n"
                 "  int signed si = -1; bit signed [7:0] sb = 8'hFF;\n"
                 "  logic unsigned [31:0] ul = -1;\n"
                 "  initial begin\n"
                 "    $display(\"by=%0d sh=%0d i=%0d lo=%0d in=%0d\", by, sh, "
                 "i, lo, in);\n"
                 "    $display(\"b=%0d l=%0d ui=%0d t=%0d\", b, l, ui, t);\n"
                 "    $display(\"si=%0d sb=%0d ul=%0d\", si, sb, ul);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "by=-56 sh=-1 i=-1 lo=-1 in=-1\n"
      "b=255 l=255 ui=4294967295 t=18446744073709551615\n"
      "si=-1 sb=-1 ul=4294967295\n");
}

TEST(TwoStateAndFourState, ConversionsIntoAClassAStructAndAPackage) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package k;\n"
                 "  int ps; int pu; byte pt;\n"
                 "endpackage\n"
                 "class C;\n"
                 "  int cs; int cu; byte ct;\n"
                 "endclass\n"
                 "module t;\n"
                 "  typedef struct { int ss; int su; byte st; } S;\n"
                 "  S s; S a [2];\n"
                 "  C c = new;\n"
                 "  byte n = -3;\n"
                 "  bit [7:0] u = 8'hFD;\n"
                 "  logic [11:0] w = 12'h3x5;\n"
                 "  initial begin\n"
                 "    k::ps = n; k::pu = u; k::pt = w;\n"
                 "    c.cs = n; c.cu = u; c.ct = w;\n"
                 "    a[1].ss = n; a[1].su = u; a[1].st = w;\n"
                 "    s.su = u; s.st = w;\n"
                 "    $display(\"%0d %0d %h\", k::ps, k::pu, k::pt);\n"
                 "    $display(\"%0d %0d %h\", c.cs, c.cu, c.ct);\n"
                 "    $display(\"%0d %0d %h\", a[1].ss, a[1].su, a[1].st);\n"
                 "    $display(\"%0d %h\", s.su, s.st);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "-3 253 05\n-3 253 05\n-3 253 05\n253 05\n");
}

TEST(TwoStateAndFourState, DISABLED_SignedValueWidenedIntoAMemberSignExtends) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int ss; } S;\n"
                       "typedef struct packed { int ps; } P;\n"
                       "typedef union packed { int a; bit [31:0] b; } U;\n"
                       "class C; S s; endclass\n"
                       "package k; S ks; endpackage\n"
                       "module t;\n"
                       "  byte n = -3;\n"
                       "  wire signed [7:0] nw = -3;\n"
                       "  S s1, s2, s3, s4, s5, s6; P p; U u; C c = new;\n"
                       "  S s7 = '{ss: 8'sd253};\n"
                       "  assign s6.ss = nw;\n"
                       "  initial begin\n"
                       "    s1.ss = n; p.ps = n; u.a = n; c.s.ss = n;\n"
                       "    k::ks.ss = n; s2.ss <= n; s3 = '{ss: n};\n"
                       "    s4 = '{n}; s5.ss = 8'sd253;\n"
                       "    #1 $display(\"%0d %0d %0d %0d %0d %0d\", s1.ss, "
                       "p.ps, u.a, c.s.ss,\n"
                       "                k::ks.ss, s2.ss);\n"
                       "    $display(\"%0d %0d %0d %0d %0d\", s3.ss, s4.ss, "
                       "s5.ss, s6.ss, s7.ss);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "-3 -3 -3 -3 -3 -3\n-3 -3 -3 -3 -3\n");
}

TEST(TwoStateAndFourState, LogicAndRegDenoteTheSameType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  task automatic tk(ref logic [3:0] a);\n"
                 "    a = 4'h5;\n"
                 "  endtask\n"
                 "  reg [3:0] r;\n"
                 "  initial begin\n"
                 "    tk(r);\n"
                 "    $display(\"%0d %0d %0d %h\", type(logic [3:0]) == "
                 "type(reg [3:0]),\n"
                 "             type(reg) == type(logic),\n"
                 "             type(bit [3:0]) == type(logic [3:0]), r);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 1 0 5\n");
}

}  // namespace
