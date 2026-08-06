

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GateArrayConnection, MatchingWidthBroadcastElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayConnection, DistributeWidthElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] y, a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §28.3.6: the connection rules are applied to each terminal independently, so
// a single instance array may distribute one terminal (width == array length)
// while broadcasting another (single-instance width). Here the output is
// distributed across the four instances and the two inputs are broadcast to
// each; the mix shall elaborate cleanly.
TEST(GateArrayConnection, MixedBroadcastAndDistributePerTerminalElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §28.3.6: the terminal-width comparison is made against the instance-array
// length, which §28.3.5 lets be given by a constant expression rather than a
// literal. A parameter-bounded range takes the parameter-resolution path (not
// the direct-literal path) when the array length is computed, and the width
// rule must still classify a same-width terminal as distributed. Here the range
// is 0:N-1 with parameter N == 4, matching the 4-bit terminals.
TEST(GateArrayConnection, ParameterizedArrayRangeDistributesAcrossInstances) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter N = 4;\n"
      "  wire [3:0] y, a, b;\n"
      "  and g[0:N-1](y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §28.3.6: the same width comparison against a parameter-derived array length
// must still flag a terminal that is neither single-instance width nor array
// length. With parameter N == 4 the array has four instances, so a 2-bit output
// has too few bits and is rejected — the error path reached through the
// parameter-resolution route rather than a literal bound.
TEST(GateArrayConnection, ParameterizedArrayRangeTooFewBitsIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter N = 4;\n"
      "  wire [1:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:N-1](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(GateArrayConnection, TooFewBitsOnArrayPortIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [1:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §28.3.6: the terminal-connection rules name *too many* bits as an error just
// as they name too few. Four instances each need a 1-bit output, so a matching
// terminal is 1 bit (broadcast) or 4 bits (distributed); an 8-bit terminal has
// surplus bits that connect to no instance and shall be rejected.
TEST(GateArrayConnection, TooManyBitsOnArrayPortIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §28.3.6: an interconnect terminal connected to an instance array must have a
// bit-length equal to the array length; it cannot be broadcast like an ordinary
// scalar net.
TEST(GateArrayConnection, ScalarInterconnectCannotBroadcastAcrossArray) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  interconnect ic;\n"
      "  wire a, b;\n"
      "  and g[0:3](ic, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(GateArrayConnection, InterconnectWidthEqualToArrayLengthElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  interconnect [3:0] ic;\n"
      "  wire a, b;\n"
      "  and g[0:3](ic, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
