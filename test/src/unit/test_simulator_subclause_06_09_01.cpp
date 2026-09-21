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

// §6.9.1: vectors obey modulo-2**n arithmetic, so subtracting past zero wraps
// around to the top of the range rather than going negative.
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

// §6.9.1: a reg/logic/bit vector is treated as an unsigned quantity by default.
// The observable consequence at run time is that widening it into a larger
// context zero-fills the high bits rather than replicating a sign bit: a 4-bit
// unsigned pattern with its top bit set carries its plain magnitude (15), not a
// sign-extended negative value. Driven through the full pipeline so the width
// and unsigned-ness of the declared vector are the production values feeding
// the widening conversion, not a hand-built vector.
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

// §6.9.1: the unsigned-by-default rule is overridden when the vector is
// declared signed. The same 4-bit pattern that a plain vector carries as 15 is
// instead interpreted as -1 and sign-extended when widened. This is the
// accepting counterpart that pins the "unless declared to be signed" exception:
// only the signed keyword on the declaration differs from
// UnsignedVectorZeroExtends, and it flips zero-extension to sign-extension.
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

// §6.9.1: because a default vector is unsigned, it can never compare as less
// than zero. A relational comparison against 0 stays unsigned when either
// operand is an unsigned vector, so a vector whose top bit is set (which a
// signed reading would call negative) is still the positive magnitude 8 and the
// comparison is false.
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

// §6.9.1: the default-unsigned rule holds across an ordinary port connection.
// This is the baseline for the signed-port exception below: a plain unsigned
// vector connected to an unsigned port is zero-extended when widened inside the
// child (top bits 0), so the port connection by itself does not change
// signedness. Built end-to-end from real §23.2.2.1 port-declaration syntax and
// run so the connection is the production path.
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

// §6.9.1: a vector is treated as unsigned unless it is connected to a port that
// is declared signed (see 23.3.3.8). The same unsigned vector that stays 0x0F
// through an unsigned port is instead interpreted as signed when the receiving
// port is declared signed, so widening inside the child sign-extends the set
// top bit to 0xFF. Only the port's signedness differs from the baseline above.
// Exercises the signed-connection semantics of dependency §23.3.3.8.
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

// §6.9.1: the signed-port exception applies however the signed port is
// declared. Here the child declares its signed port in the non-ANSI style
// (dependency §23.2.2.1) rather than in the header, and the unsigned vector is
// still interpreted as signed across the connection and sign-extended to 0xFF.
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

// §6.9.1: the two bounds of a range may be any integer, negative included, and
// each index addresses its own bit, the msb being the left-hand value: on
// `logic [-1:4] b` holding 6'b100001, b[-1] is the most significant bit, 1,
// and b[4] the least significant, 1, with $bits 6 and the value 33. Both read
// wrong -- b[4] 0 and b[-1] x -- because RecordPackedRange read the declared
// `-1` as the 32-bit magnitude 4294967295, saw a span that did not account
// for the six bits, and left the vector addressed as [5:0]. The signed and
// wrapping lines and the ordinary [3:0] selects stand beside as the probe
// wrote them.
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

// The same range written through: on `logic [-1:4] b` a write to b[-1]
// lands on the most significant bit and one to b[4] on the least, and the
// part-select b[-1:0] is the top two bits; a range of two negative bounds,
// `logic [-2:-5] n`, addresses n[-5] as its least significant bit and n[-2]
// as its most. Addressed as [5:0], the writes to b[-1] and n[-2] are out
// of range and change nothing.
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
