#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(VectorSpecification, Modulo2nWrap) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 5'b10001;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64() & 0xF, 1u);
}

TEST(VectorSpecification, OverflowAdditionWraps) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 4'd15 + 4'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64() & 0xF, 0u);
}

// §6.9.1: vectors obey modulo-2**n arithmetic, so subtracting past zero wraps
// around to the top of the range rather than going negative.
TEST(VectorSpecification, UnderflowSubtractionWraps) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 4'd0 - 4'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64() & 0xF, 15u);
}

TEST(VectorSpecification, MaxValueFitsInVector) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial v = 255;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  LowerAndRun(design, f);

  auto* var = f.ctx.FindVariable("v");
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

}  // namespace
