#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ParameterSelectSim, OutOfRangeSelectOfAFourStateParameterReadsX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  parameter logic [7:0] P = 8'hFF;\n"
      "  localparam logic Q = P[9];\n"
      "  localparam logic [3:0] R = P[9:6];\n"
      "  parameter logic [127:0] W = {64'h1, 64'hFFFF_FFFF_FFFF_FFFF};\n"
      "  localparam logic [63:0] L = W[63:0];\n"
      "  initial $display(\"%b %b %h\", Q, R, L);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x xx11 ffffffffffffffff\n");
}

TEST(SelectAddressSim, IndexWiderThanSixtyFourBitsIsOutOfBounds) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] v = 8'hFF;\n"
      "  logic [64:0] i = {1'b1, 64'd3};\n"
      "  logic [63:0] j = 64'h8000_0000_0000_0003;\n"
      "  logic signed [64:0] k = -65'sd1;\n"
      "  logic signed [64:0] m = {2'b01, 63'd3};\n"
      "  logic [64:0] n = 65'd3;\n"
      "  initial begin\n"
      "    $display(\"%b %b %b %b %b %b\", v[i], v[j], v[k], v[m], v[n],\n"
      "             v[i +: 2]);\n"
      "    v[i] = 1'b0;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x x x x 1 xx\nff\n");
}

TEST(SelfDeterminedSelectSim,
     EachSelectExpressionKeepsItsOwnWidthWhenReadAndWritten) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module m;\n"
                "  logic [7:0] v = 8'b1000_0001;\n"
                "  logic [1:0] i = 3, j = 1;\n"
                "  logic [2:0] u = 0;\n"
                "  logic [15:0] r;\n"
                "  logic signed [15:0] sr;\n"
                "  logic [7:0] w;\n"
                "  wire c = v[i + j];\n"
                "  wire [1:0] c2 = v[i + j +: 2];\n"
                "  initial begin\n"
                "    #1;\n"
                "    $display(\"%b %b %b %b %b\", v[i + j], v[i + j +: 2],\n"
                "             v[i + j + 2'd1 -: 2], c, c2);\n"
                "    r = v[i + j] + 16'd0;\n"
                "    sr = v[u - 1'b1] + 16'sd0;\n"
                "    $display(\"%0d %0d\", r, sr);\n"
                "    w = 0; w[i + j] = 1; $write(\"%b \", w);\n"
                "    w = 0; w[i + j +: 2] = 2'b11; $write(\"%b \", w);\n"
                "    w = 0; w[i + j + 2'd1 -: 2] = 2'b11; $write(\"%b \", w);\n"
                "    w = 0; w[i + j] <= 1; #1 $display(\"%b\", w);\n"
                "  end\n"
                "endmodule\n",
                f),
            "1 01 01 1 01\n1 1\n00000001 00000011 00000011 00000001\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SelfDeterminedSelectSim, ConstantSelectExpressionsKeepTheirOwnWidth) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m;\n"
          "  localparam logic [1:0] A = 3, B = 1, W1 = 3, W2 = 3;\n"
          "  localparam logic [7:0] PV = 8'b1000_0001;\n"
          "  localparam logic [1:0] L1 = PV[A + B +: 2];\n"
          "  localparam logic [7:0] L2 = PV[A + B];\n"
          "  localparam int L3 = $bits(PV[A + B : 0]);\n"
          "  localparam int L4 = $bits(PV[0 +: W1 + W2]);\n"
          "  logic [7:0] v = PV;\n"
          "  initial\n"
          "    $display(\"%b %b %0d %0d %0d %0d %b %b\", L1, L2, L3, L4,\n"
          "             $bits(v[A + B : 0]), $bits(v[0 +: W1 + W2]),\n"
          "             v[A + B : 0], v[0 +: W1 + W2]);\n"
          "endmodule\n",
          f),
      "01 00000001 1 2 1 2 1 01\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SelectAddressSim, TheBitAddressingExamplesGiveTheirBits) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m;\n"
          "  logic [31:0] a_vect = 32'h12345678;\n"
          "  logic [0:31] b_vect = 32'h12345678;\n"
          "  logic [63:0] dword = 64'h0123456789abcdef;\n"
          "  integer sel = 2;\n"
          "  logic [7:0] vect;\n"
          "  bit [7:0] bv = 8'hff;\n"
          "  logic [3:0] addr;\n"
          "  initial begin\n"
          "    $display(\"%h %h %h %h %h\", a_vect[0 +: 8], a_vect[15 -: 8],\n"
          "             b_vect[0 +: 8], b_vect[15 -: 8], dword[8*sel +: 8]);\n"
          "    vect = 4;\n"
          "    addr = 2; $write(\"%b \", vect[addr]);\n"
          "    addr = 9; $write(\"%b \", vect[addr]);\n"
          "    addr = 0; $write(\"%b \", vect[addr]);\n"
          "    addr = 3; $write(\"%b \", vect[addr]);\n"
          "    addr = 7; $display(\"%b\", vect[addr]);\n"
          "    $write(\"%b %b \", vect[3:0], vect[5:1]);\n"
          "    $write(\"%b %b \", vect[1'bx + 1], vect[1'bz]);\n"
          "    addr = 4'b0x10; $write(\"%b %b \", vect[addr], bv[addr]);\n"
          "    addr = 4'b001z; $display(\"%b %b\", vect[addr], bv[addr]);\n"
          "  end\n"
          "endmodule\n",
          f),
      "78 56 12 34 ab\n1 x 0 0 0\n0100 00010 x x x 0 x 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
