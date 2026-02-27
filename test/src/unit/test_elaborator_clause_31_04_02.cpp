// §31.4.2: $timeskew

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $timeskew_timing_check — with flags
// =============================================================================
TEST(ElabA70501, TimeskewWithFlagsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
