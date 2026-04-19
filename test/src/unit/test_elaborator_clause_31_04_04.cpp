#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.4.4 Syntax 31-12: the bare two-argument `$width` form with an
// edge-qualified reference event must elaborate without errors.
TEST(TimingCheckCommandElaboration, WidthBasicElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, 20);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.4 Table 31-10: the four-argument form with explicit threshold and
// notifier must elaborate.
TEST(TimingCheckCommandElaboration, WidthWithThresholdAndNotifierElaborates) {
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

// §31.4.4 Table 31-10: timing_check_limit and threshold are constant
// expressions, so specparam-bound values must elaborate.
TEST(TimingCheckCommandElaboration, WidthWithSpecparamsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam lim = 20;\n"
      "    specparam thr = 1;\n"
      "    $width(posedge clk, lim, thr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
