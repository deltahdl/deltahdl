// §31.4.3: $fullskew

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $fullskew_timing_check — with flags
// =============================================================================
TEST(ElabA70501, FullskewWithFlagsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr, 1, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
