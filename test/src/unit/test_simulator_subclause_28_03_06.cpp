#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(GateArrayRuntime, NInputArrayDistributesPerBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] a, b;\n"
      "  wire [3:0] y;\n"
      "  initial begin a = 4'b1100; b = 4'b1010; end\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 0xFu, 0x8u);
  EXPECT_EQ(w.bval & 0xFu, 0x0u);
}

TEST(GateArrayRuntime, ScalarEnableBroadcastsAcrossThreeStateArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] in;\n"
      "  logic en;\n"
      "  wire [3:0] out;\n"
      "  initial begin in = 4'b1011; en = 1'b0; end\n"
      "  bufif0 ar[3:0](out, in, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("out");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 0xFu, 0xBu);
  EXPECT_EQ(w.bval & 0xFu, 0x0u);
}

TEST(GateArrayRuntime, DistributedEnableAppliesPerElementControl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] in, en;\n"
      "  wire [3:0] out;\n"
      "  initial begin in = 4'b1111; en = 4'b1010; end\n"
      "  bufif0 ar[3:0](out, in, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("out");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 0xFu, 0x5u);
}

TEST(GateArrayRuntime, DistributedTerminalChangeReevaluatesEachElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] a, b;\n"
      "  wire [3:0] y;\n"
      "  initial begin\n"
      "    a = 4'b1100; b = 4'b1010;\n"
      "    #10 b = 4'b0101;\n"
      "  end\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 0xFu, 0x4u);
  EXPECT_EQ(w.bval & 0xFu, 0x0u);
}

TEST(GateArrayRuntime, ExampleTwoDriverAndDriverEquivAgree) {
  SimFixture f;
  auto out = RunCapture(
      "module driver (in, out, en);\n"
      "  input [3:0] in;\n"
      "  output [3:0] out;\n"
      "  input en;\n"
      "  bufif0 ar[3:0] (out, in, en);\n"
      "endmodule\n"
      "module driver_equiv (in, out, en);\n"
      "  input [3:0] in;\n"
      "  output [3:0] out;\n"
      "  input en;\n"
      "  bufif0 ar3 (out[3], in[3], en);\n"
      "  bufif0 ar2 (out[2], in[2], en);\n"
      "  bufif0 ar1 (out[1], in[1], en);\n"
      "  bufif0 ar0 (out[0], in[0], en);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] in = 4'b1010;\n"
      "  logic en = 0;\n"
      "  wire [3:0] o1, o2;\n"
      "  driver d1 (in, o1, en);\n"
      "  driver_equiv d2 (in, o2, en);\n"
      "  initial begin\n"
      "    #1 $display(\"o1=%b o2=%b\", o1, o2);\n"
      "    in = 4'b0110;\n"
      "    #1 $display(\"o1=%b o2=%b\", o1, o2);\n"
      "    en = 1;\n"
      "    #1 $display(\"o1=%b o2=%b\", o1, o2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "o1=1010 o2=1010\n"
            "o1=0110 o2=0110\n"
            "o1=zzzz o2=zzzz\n");
}

TEST(GateArrayRuntime, ArrayOnASubmodulesVectorPortsDistributesPerBit) {
  SimFixture f;
  auto out = RunCapture(
      "module m (output [3:0] y, input [3:0] a, b);\n"
      "  xor g[3:0] (y, a, b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] a = 4'b1100, b = 4'b1111;\n"
      "  wire [3:0] y;\n"
      "  m i (y, a, b);\n"
      "  initial begin\n"
      "    #1 $display(\"y=%b\", y);\n"
      "    b = 4'b0010;\n"
      "    #1 $display(\"y=%b\", y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "y=0011\n"
            "y=1110\n");
}

TEST(GateArrayRuntime, ArrayRangeFromAModuleParameterOnItsPorts) {
  SimFixture f;
  auto out = RunCapture(
      "module inv #(parameter N = 2) (output [N-1:0] y, input [N-1:0] a);\n"
      "  not g[N-1:0] (y, a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] y;\n"
      "  logic [7:0] a = 8'b11000011;\n"
      "  inv #(8) i (y, a);\n"
      "  int n;\n"
      "  initial begin\n"
      "    #1 n = 0;\n"
      "    for (int k = 0; k < 8; k++) n += y[k];\n"
      "    $display(\"y=%b n=%0d\", y, n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=00111100 n=4\n");
}

TEST(GateArrayRuntime, GateInputOnABitSelectOfAnInputPort) {
  SimFixture f;
  auto out = RunCapture(
      "module m (output y0, y1, y2, y3, input [1:0] a);\n"
      "  wire [1:0] t = a;\n"
      "  not ga (y0, a[0]);\n"
      "  not gb (y1, a[1]);\n"
      "  not gc (y2, t[0]);\n"
      "  not gd (y3, t[1]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [1:0] a2 = 2'b10;\n"
      "  wire y0, y1, y2, y3;\n"
      "  m i (y0, y1, y2, y3, a2);\n"
      "  initial begin\n"
      "    #1 $display(\"y0=%b y1=%b y2=%b y3=%b\", y0, y1, y2, y3);\n"
      "    a2 = 2'b01;\n"
      "    #1 $display(\"y0=%b y1=%b y2=%b y3=%b\", y0, y1, y2, y3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "y0=1 y1=0 y2=1 y3=0\n"
            "y0=0 y1=1 y2=0 y3=1\n");
}

TEST(GateArrayRuntime, GateOutputOnABitSelectOfAnOutputPort) {
  SimFixture f;
  auto out = RunCapture(
      "module m (output [1:0] y, input a);\n"
      "  not g0 (y[0], a);\n"
      "  buf g1 (y[1], a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a = 1;\n"
      "  wire [1:0] y;\n"
      "  m i (y, a);\n"
      "  initial begin\n"
      "    #1 $display(\"y=%b\", y);\n"
      "    a = 0;\n"
      "    #1 $display(\"y=%b\", y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "y=10\n"
            "y=01\n");
}

TEST(GateArrayRuntime, ATerminalsBitsFollowItsDeclaredRange) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  wire [3:0] y;\n"
      "  wire [0:3] a = 4'b0001;\n"
      "  wire [4:1] z;\n"
      "  wire [4:1] b = 4'b1000;\n"
      "  buf g[3:0] (y, a);\n"
      "  buf h[3:0] (z, b);\n"
      "  initial #1 $display(\"%b %b\", y, z);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0001 1000\n");
}

TEST(GateArrayRuntime, SelectsAndConcatenationsAreSharedOutPerInstance) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  wire [7:0] a = 8'hA5;\n"
      "  wire [7:0] c = 8'b0000_0110;\n"
      "  wire [7:0] d = 8'b0110_0000;\n"
      "  wire [7:0] e = 8'b1100_0000;\n"
      "  wire [3:0] y, w, v;\n"
      "  bufif1 g[3:0] (y, a[3:0], c[3:0]);\n"
      "  buf h[3:0] ({w[1:0], w[3:2]}, d[4 +: 4]);\n"
      "  buf k[3:0] (v, e[7 -: 4]);\n"
      "  initial #1 $display(\"%b %b %b\", y, w, v);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "z10z 1001 1100\n");
}

TEST(GateArrayRuntime, AnOperatorExpressionTerminalIsSharedOutPerInstance) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  wire [3:0] a = 4'b0101, b = 4'b0011, c = 4'b0110;\n"
      "  wire [3:0] y1, y2, y3, y4, y5;\n"
      "  bufif1 g1[3:0] (y1, a & b, c);\n"
      "  buf g2[3:0] (y2, a | b);\n"
      "  buf g3[3:0] (y3, a ^ b);\n"
      "  buf g4[3:0] (y4, ~a);\n"
      "  buf g5[3:0] (y5, !c);\n"
      "  initial #1 $display(\"%b %b %b %b %b\", y1, y2, y3, y4, y5);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "z00z 0111 0110 1010 0000\n");
}

TEST(GateArrayRuntime, ABitwiseTerminalExtendsEachOperandToItsWidth) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  wire [3:0] a = 4'b0101;\n"
      "  wire [1:0] c = 2'b11;\n"
      "  wire s1 = 1'b1;\n"
      "  wire signed [3:0] sa = 4'sb0101;\n"
      "  wire signed [1:0] sc = 2'sb10;\n"
      "  wire signed ss = 1'b1;\n"
      "  wire [3:0] y1, y2, y3, y4, y5, y6, y7, y8, y9;\n"
      "  buf g1[3:0] (y1, a | c);\n"
      "  buf g2[3:0] (y2, sa | sc);\n"
      "  buf g3[3:0] (y3, a ^ s1);\n"
      "  buf g4[3:0] (y4, ~(sa & sc));\n"
      "  buf g5[3:0] (y5, sa ^ ss);\n"
      "  buf g6[3:0] (y6, sa | 2'sb10);\n"
      "  buf g7[3:0] (y7, sa | sc[1:0]);\n"
      "  buf g8[3:0] (y8, a & (c + c));\n"
      "  buf g9[3:0] (y9, (c + c) & a);\n"
      "  initial #1 $display(\"%b %b %b %b %b %b %b %b %b\",\n"
      "                      y1, y2, y3, y4, y5, y6, y7, y8, y9);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0111 1111 0100 1011 1010 1111 0111 0100 0100\n");
}

TEST(GateArrayRuntime, ALiteralTerminalIsSharedOutPerInstance) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  wire [3:0] w, v, u;\n"
      "  buf g[3:0] (w, 4'b1100);\n"
      "  buf h[3:0] (v, {2'b10, 1'b0, 1'b1});\n"
      "  buf k[3:0] (u, 4'b10xz);\n"
      "  initial #1 $display(\"%b %b %b\", w, v, u);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1100 1001 10xx\n");
}

TEST(GateArrayRuntime, ASubarrayOrAnUnpackedElementIsSharedOutPerInstance) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  localparam logic [1:0] P = 2'b01;\n"
      "  wire [1:0][1:0] p = 4'b1000;\n"
      "  logic [1:0] mem [0:1];\n"
      "  integer n = 1;\n"
      "  wire [1:0] y, z, x, w;\n"
      "  buf g[1:0] (y, p[1]);\n"
      "  buf h[1:0] (z, mem[1]);\n"
      "  buf k[1:0] (x, n[0]);\n"
      "  buf q[1:0] (w, P[0]);\n"
      "  initial mem[1] = 2'b10;\n"
      "  initial #1 $display(\"%b %b %b %b\", y, z, x, w);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "10 10 11 11\n");
}

}  // namespace
