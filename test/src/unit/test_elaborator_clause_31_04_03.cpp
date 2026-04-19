#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.4.3 Syntax 31-11: bare $fullskew with edge-qualified reference and
// data events plus two constant limits must elaborate cleanly.
TEST(SystemTimingCheckElaboration, FullskewElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, 6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.3 Syntax 31-11 / Table 31-9: the two trailing optional slots —
// event_based_flag and remain_active_flag — must flow through elaboration
// alongside the notifier and the two positional limits.
TEST(TimingCheckCommandElaboration, FullskewWithFlagsElaborates) {
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

// §31.4.3 Table 31-9: the optional notifier slot resolves to a variable
// identifier and must elaborate alongside the two limits.
TEST(SystemTimingCheckElaboration, FullskewWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.3 Table 31-9: the limits are non-negative *constant* expressions,
// so indirection through specparams in either limit slot must elaborate.
TEST(SystemTimingCheckElaboration, FullskewSpecparamLimitsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tLo = 4;\n"
      "    specparam tHi = 6;\n"
      "    $fullskew(posedge clk1, negedge clk2, tLo, tHi);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.3: the literal zero is a valid non-negative constant — the LRM
// explicitly defines $fullskew's behaviour when the skew limit value is
// zero, so the boundary must elaborate.
TEST(SystemTimingCheckElaboration, FullskewZeroLimitsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, 0, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
