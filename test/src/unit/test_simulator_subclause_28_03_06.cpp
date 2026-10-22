#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §28.3.6: when a terminal's width equals the instance-array length it is
// distributed — each element connects to its own bit of the terminal. A row of
// four `and` gates over 4-bit terminals therefore computes the bitwise AND, one
// bit per element, rather than any whole-word reduction.
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
  // 1100 & 1010 == 1000
  EXPECT_EQ(w.aval & 0xFu, 0x8u);
  EXPECT_EQ(w.bval & 0xFu, 0x0u);
}

// §28.3.6: a single-bit terminal is broadcast to every element of the array.
// This is the LRM's own three-state array example — a scalar enable feeding a
// row of buffers whose data and outputs are distributed. With the enable
// asserted for conduction, every element passes its own data bit, so the output
// word equals the input word.
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
  // en == 0 conducts on every element, so out == in == 1011.
  EXPECT_EQ(w.aval & 0xFu, 0xBu);
  EXPECT_EQ(w.bval & 0xFu, 0x0u);
}

// §28.3.6: a distributed control terminal is likewise part-selected per element
// — each buffer sees only its own enable bit, not a word-wide reduction of the
// whole control vector. With enable 1010 a bufif0 row conducts on the bits
// whose enable is 0 (bits 0 and 2), so those output bits follow their data
// while the disabled bits are not driven to a logic 1. The word-reduced
// (pre-fix) result would have turned the entire array off.
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
  // Conducting bits (enable 0) are bits 0 and 2, each passing its data bit 1.
  EXPECT_EQ(w.aval & 0xFu, 0x5u);
}

// §28.3.6's Example 2 states that `bufif0 ar[3:0] (out, in, en);` and the four
// separate declarations `bufif0 ar3 (out[3], in[3], en);` and so on are
// the same apart from the indexed instance names, so an element of an array
// answers a later change of its own input bit exactly as the separate
// declaration would. The three cases above drive their inputs once and read the
// settled value, which holds however the elements are woken.
//
// b alone changes at time 10 and a is held still, so a watcher armed on a
// cannot carry it: 1100 & 1010 is 1000 and 1100 & 0101 is 0100. An array whose
// elements stopped after their first evaluation reads 1000.
//
// A gate array reaches the same watch-list walk a UDP array does -- both expand
// through ExpandInstanceArray, and the coroutine collects its reads with
// CollectExprReads -- so this case and the §29.8 one stand over one collection
// through two lowerings.
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
  // 1100 & 0101 == 0100
  EXPECT_EQ(w.aval & 0xFu, 0x4u);
  EXPECT_EQ(w.bval & 0xFu, 0x0u);
}

// §28.3.6 (printed page 833), Example 2: `driver`'s `bufif0 ar[3:0] (out, in,
// en)` on the module's own vector ports and `driver_equiv`'s four buffers, each
// on one bit-select of those ports, differ in nothing but the indexed instance
// names, so the two drive the same values onto the nets the parent connects,
// and both output z once the shared enable turns them off.
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

// §28.3.6: an array of xor gates inside a module, on the module's vector ports
// (§23.2.2), takes each bit of the ports to its own instance, the LSB to the
// right-hand index, and re-evaluates each instance when the parent changes an
// input after time 0.
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

// §28.3.6 with §23.2.2: the array's range may be written with the module's
// parameter, `not g[N-1:0] (y, a)` under `#(8)`, and still takes one bit of
// each eight-bit port per instance.
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

// §28.3.6: a single gate's input terminal may be any expression, a bit-select
// of the module's input port or of a wire continuously assigned from it
// included, and follows the port when the parent changes it.
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

// §28.3.6: a single gate's output terminal may be a bit-select of the module's
// vector output port, and each gate drives its own bit of the net the parent
// connects.
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

// §28.3.6 gives the least significant bit of a terminal wider than one
// instance's to the instance of the array range's right-hand index, and the
// next bits to the instances after it, whatever range the terminal was
// declared with: a's least significant bit is a[3] and b's most significant
// b[4]. Selected at its element's number as an index of the declared range,
// a[0] went to instance [0] and b[0], out of range, besides.
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

// A part-select, an indexed part-select or a concatenation as wide as the array
// is shared out a bit per instance as a named vector is: each bufif1 takes one
// bit of a[3:0] under one bit of c[3:0], and the outputs reach the bits of y
// through the concatenation, y[3:2] taking its low two. Connected whole, every
// instance drove all four bits under one control.
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

// An input terminal is any expression, and one as wide as the array is shared
// out a bit per instance like a named vector: the bitwise &, | and ^ of two
// four-bit vectors, and the ~ of one, are four bits each. An operator the
// width is not read through, a +, connects whole. Measured as nothing, each
// operator terminal was connected whole to every instance.
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

// A literal terminal is measured by its bit length as any other expression is,
// a sized literal's being its size (§5.7.1), so one as wide as the array is
// shared out a bit per instance: g[k] buffers bit k of 4'b1100, h[k] bit k of
// the concatenation, and k[k] bit k of 4'b10xz, a buf turning its z into x.
// Measured as nothing, each literal was connected whole, and every instance
// read its least significant bit: 0000 1111 xxxx.
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

}  // namespace
