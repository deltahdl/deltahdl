#include <gtest/gtest.h>

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

}  // namespace
