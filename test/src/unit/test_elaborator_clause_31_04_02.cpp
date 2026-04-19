#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.4.2 Syntax 31-10: bare $timeskew with edge-qualified reference and
// data events plus a constant timing_check_limit must elaborate cleanly.
TEST(SystemTimingCheckElaboration, TimeskewElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.2 Syntax 31-10 / Table 31-8: the optional notifier slot resolves to
// a variable identifier and must elaborate.
TEST(SystemTimingCheckElaboration, TimeskewWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.2 Syntax 31-10: the trailing optional event_based_flag and
// remain_active_flag arguments must flow through elaboration.
TEST(TimingCheckCommandElaboration, TimeskewWithFlagsElaborates) {
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

// §31.4.2 Table 31-8: the limit is a non-negative *constant* expression, so
// indirection through a specparam must elaborate.
TEST(SystemTimingCheckElaboration, TimeskewSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = 7;\n"
      "    $timeskew(posedge clk1, posedge clk2, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.2: the literal zero is a valid non-negative constant — the LRM
// explicitly defines $timeskew's behaviour when the skew limit value is
// zero, so the boundary must elaborate.
TEST(SystemTimingCheckElaboration, TimeskewZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
