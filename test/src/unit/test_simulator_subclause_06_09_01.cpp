#include <gtest/gtest.h>

#include <format>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(VectorSpecification, Modulo2nWrap) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 5'b10001;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64() & 0xF, 1u);
}

TEST(VectorSpecification, OverflowAdditionWraps) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 4'd15 + 4'd1;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64() & 0xF, 0u);
}

TEST(VectorSpecification, UnderflowSubtractionWraps) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 4'd0 - 4'd1;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64() & 0xF, 15u);
}

TEST(VectorSpecification, MaxValueFitsInVector) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial v = 255;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFF, 255u);
}

TEST(VectorSpecification, UnsignedVectorZeroExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [3:0] u;\n"
      "  int w;\n"
      "  initial begin\n"
      "    u = 4'b1111;\n"
      "    w = u;\n"
      "  end\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(v, 15u);
}

TEST(VectorSpecification, SignedVectorSignExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  int w;\n"
      "  initial begin\n"
      "    s = 4'b1111;\n"
      "    w = s;\n"
      "  end\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(v, 0xFFFFFFFFu);
}

TEST(VectorSpecification, UnsignedVectorNeverBelowZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [3:0] u;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    u = 4'b1000;\n"
      "    r = (u < 0);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0u);
}

TEST(VectorSpecification, UnsignedVectorThroughUnsignedPortStaysUnsigned) {
  auto v = RunAndGet(
      "module child(input logic [3:0] p, output logic [7:0] o);\n"
      "  assign o = p;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [3:0] u;\n"
      "  logic [7:0] o;\n"
      "  child c(.p(u), .o(o));\n"
      "  initial u = 4'b1111;\n"
      "endmodule\n",
      "o");
  EXPECT_EQ(v & 0xFFu, 0x0Fu);
}

TEST(VectorSpecification, UnsignedVectorThroughSignedPortTreatedAsSigned) {
  auto v = RunAndGet(
      "module child(input logic signed [3:0] p, output logic [7:0] o);\n"
      "  assign o = p;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [3:0] u;\n"
      "  logic [7:0] o;\n"
      "  child c(.p(u), .o(o));\n"
      "  initial u = 4'b1111;\n"
      "endmodule\n",
      "o");
  EXPECT_EQ(v & 0xFFu, 0xFFu);
}

TEST(VectorSpecification,
     UnsignedVectorThroughNonAnsiSignedPortTreatedAsSigned) {
  auto v = RunAndGet(
      "module child(p, o);\n"
      "  input signed [3:0] p;\n"
      "  output [7:0] o;\n"
      "  assign o = p;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [3:0] u;\n"
      "  logic [7:0] o;\n"
      "  child c(.p(u), .o(o));\n"
      "  initial u = 4'b1111;\n"
      "endmodule\n",
      "o");
  EXPECT_EQ(v & 0xFFu, 0xFFu);
}

TEST(VectorSpecification, NegativeBoundAddressesItsOwnBit) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  logic [-1:4] b;\n"
                 "  logic signed [3:0] sr, sr2;\n"
                 "  logic [3:0] v;\n"
                 "  bit [3:0] wrap;\n"
                 "  initial begin\n"
                 "    b = 6'b100001;\n"
                 "    $display(\"bits=%0d b=%0d b4=%0d bm1=%0d\", $bits(b), b, "
                 "b[4], b[-1]);\n"
                 "    sr = 8; sr2 = 7;\n"
                 "    wrap = 15; wrap = wrap + 1;\n"
                 "    $display(\"sr=%0d sr2=%0d wrap=%0d\", sr, sr2, wrap);\n"
                 "    v = 4'b1010;\n"
                 "    $display(\"v3=%0d v0=%0d v=%b\", v[3], v[0], v);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "bits=6 b=33 b4=1 bm1=1\n"
      "sr=-8 sr2=7 wrap=0\n"
      "v3=1 v0=0 v=1010\n");
}

TEST(VectorSpecification, NegativeBoundIsWrittenThrough) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [-1:4] b;\n"
                       "  logic [-2:-5] n;\n"
                       "  initial begin\n"
                       "    b = 6'b000000; n = 4'b0000;\n"
                       "    b[-1] = 1'b1; b[4] = 1'b1;\n"
                       "    $display(\"b=%b hi=%b\", b, b[-1:0]);\n"
                       "    n[-2] = 1'b1; n[-5] = 1'b1; n[-4] = 1'b1;\n"
                       "    $display(\"n=%b n4=%b n3=%b\", n, n[-4], n[-3]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "b=100001 hi=10\n"
            "n=1011 n4=1 n3=0\n");
}

TEST(VectorSpecification, ExampleDeclarationsTakeTheirWidths) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  wand w;\n"
                       "  tri [15:0] busa;\n"
                       "  trireg (small) storeit;\n"
                       "  logic a;\n"
                       "  logic [3:0] v;\n"
                       "  logic [-1:4] b;\n"
                       "  wire w1, w2;\n"
                       "  logic [4:0] x, y, z;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d %0d %0d %0d "
                       "%0d %0d %0d\",\n"
                       "                   $bits(w), $bits(busa), "
                       "$bits(storeit), $bits(a),\n"
                       "                   $bits(v), $bits(b), $bits(w1), "
                       "$bits(w2), $bits(x),\n"
                       "                   $bits(y), $bits(z));\n"
                       "endmodule\n",
                       f),
            "1 16 1 1 4 6 1 1 5 5 5\n");
}

TEST(VectorSpecification, MsbIsTheLeftBoundAndLsbTheRight) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [3:0] v;\n"
                       "  logic [0:3] r;\n"
                       "  initial begin\n"
                       "    v = 4'b1000;\n"
                       "    r = 4'b1000;\n"
                       "    $display(\"%b%b%b%b %b%b%b%b\", v[3], v[2], v[1], "
                       "v[0], r[0],\n"
                       "             r[1], r[2], r[3]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1000 1000\n");
}

TEST(VectorSpecification, FourBitSignedVectorHoldsMinusEightToSeven) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic signed [3:0] signed_reg;\n"
                       "  initial begin\n"
                       "    signed_reg = 7;\n"
                       "    $display(\"%0d\", signed_reg);\n"
                       "    signed_reg = 8;\n"
                       "    $display(\"%0d\", signed_reg);\n"
                       "    signed_reg = -8;\n"
                       "    $display(\"%0d\", signed_reg);\n"
                       "    signed_reg = -9;\n"
                       "    $display(\"%0d\", signed_reg);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7\n-8\n-8\n7\n");
}

TEST(VectorSpecification, VectorOfTheGuaranteedLengthHoldsEveryBit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [65535:0] v;\n"
                       "  initial begin\n"
                       "    v = 0;\n"
                       "    v[65535] = 1;\n"
                       "    v[0] = 1;\n"
                       "    $display(\"%0d %b %b %b\", $bits(v), v[65535], "
                       "v[65534], v[0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "65536 1 0 1\n");
}

constexpr std::string_view kScopeVectors =
    "  parameter W = 4;\n"
    "  logic [W-1:0] a = 4'hC;\n"
    "  bit [W*2-1:0] c = 8'hC3;\n"
    "  logic [1:0][W-1:0] v = 8'hC3;\n"
    "  var logic [W*2-1:0] ub;\n"
    "  localparam L = 3;\n"
    "  typedef logic [L:0] t;\n"
    "  t d = 4'hA;\n"
    "  localparam logic [W-1:0] P = 4'hB;\n"
    "  logic [3:0] lit = 4'h9;\n"
    "  logic [W:0] e [2];\n"
    "  logic [W:0] md [2][3];\n"
    "  logic [W-1:0] dq [];\n"
    "  logic [W-1:0] qu [$];\n"
    "  logic [W-1:0] aa [int];\n";

constexpr std::string_view kScopeVectorsPrinted =
    "4 c 8 c3 8 c3 c 8 4 a 4 b 4 9 5 1f 5 1f f b b\n";

std::string ScopeVectorReads(std::string_view prefix) {
  return std::format(
      "  initial begin\n"
      "    {0}e[1] = 8'hFF;\n"
      "    {0}md[1][2] = 8'hFF;\n"
      "    {0}dq = new[1];\n"
      "    {0}dq[0] = 8'hFF;\n"
      "    {0}qu.push_back(8'hAB);\n"
      "    {0}aa[1] = 8'hAB;\n"
      "    $display(\"%0d %h %0d %h %0d %h %h %0d %0d %h %0d %h %0d %h %0d "
      "%h %0d %h %h %h %h\",\n"
      "        $bits({0}a), {0}a, $bits({0}c), {0}c, $bits({0}v), {0}v,\n"
      "        {0}v[1], $bits({0}ub), $bits({0}d), {0}d, $bits({0}P), {0}P,\n"
      "        $bits({0}lit), {0}lit, $bits({0}e[0]), {0}e[1],\n"
      "        $bits({0}md[1][2]), {0}md[1][2], {0}dq[0], {0}qu[0], "
      "{0}aa[1]);\n"
      "  end\n",
      prefix);
}

TEST(VectorSpecification,
     PackageVectorWhoseRangeNamesItsOwnParameterTakesItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::format("package pk;\n{}endpackage\n"
                                   "module top;\n{}endmodule\n",
                                   kScopeVectors, ScopeVectorReads("pk::")),
                       f),
            kScopeVectorsPrinted);
}

TEST(VectorSpecification,
     CompilationUnitVectorWhoseRangeNamesItsOwnParameterTakesItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::format("{}module top;\n{}endmodule\n",
                                   kScopeVectors, ScopeVectorReads("")),
                       f),
            kScopeVectorsPrinted);
}

}  // namespace
