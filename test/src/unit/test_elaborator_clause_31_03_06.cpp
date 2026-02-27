// §31.3.6: $recrem

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $recrem_timing_check — full 9-argument form
// =============================================================================
TEST(ElabA70501, RecremFullArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
