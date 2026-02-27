// §31.4.4: $width

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $width_timing_check — threshold argument
// =============================================================================
TEST(ElabA70501, WidthWithThresholdElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, 20, 1, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
