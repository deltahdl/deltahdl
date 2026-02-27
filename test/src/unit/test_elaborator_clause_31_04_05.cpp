// §31.4.5: $period

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.3 Elab — controlled_timing_check_event
// =============================================================================
// $period with controlled_timing_check_event elaborates
TEST(ElabA70503, ControlledTimingCheckEventPeriodElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $period(posedge clk, 50);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
