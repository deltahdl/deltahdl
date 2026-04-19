#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.9: the elaborator must accept a $setuphold invocation whose
// setup and hold limits are negative. §31.3.3's elaboration rules
// say nothing about sign; the allowance lives in §31.9, and blocking
// it here would make the downstream simulator path unreachable.
TEST(NegativeTimingChecks, SetupholdNegativeLimitsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, -10, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.9: the same rule applies to $recrem — the two kinds must behave
// identically with respect to negative values, so the elaborator must
// accept either one.
TEST(NegativeTimingChecks, RecremNegativeLimitsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, -8, -3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
