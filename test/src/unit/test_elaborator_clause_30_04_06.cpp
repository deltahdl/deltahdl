#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(MultiplePathDeclarationElaboration, MixedTerminalFormsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a, b[3], intf.sig[7:0] *> x[0], y, intf2.out) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.6: a multi-path full-connection declaration may mix scalars and
// vectors of different widths on both sides; parallel-connection width
// rules from §30.4.5 do not apply.
TEST(MultiplePathDeclarationElaboration, MixedWidthsInBothLists) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input [3:0] b, input [7:0] c,\n"
      "         output x, output [15:0] y);\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 4;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
