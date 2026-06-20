

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
