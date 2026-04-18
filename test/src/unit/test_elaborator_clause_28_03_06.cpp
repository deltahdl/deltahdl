// §28.3.6 — Primitive instance connection list, array-of-instances bit-length
// rules.
//
// Each test here drives the elaborator-level checks for an array-of-instances
// whose port-expression width is compared against the per-instance port width.

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

TEST(GateArrayConnection, TooManyBitsOnArrayPortIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [5:0] y;\n"
      "  wire a, b;\n"
      "  and g[0:3](y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
