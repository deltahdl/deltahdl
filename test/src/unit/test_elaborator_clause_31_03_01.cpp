// §31.3.1: $setup

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5 system_timing_check — Elaboration
// =============================================================================
// $setup timing check elaborates
TEST(ElabA705, SetupTimingCheckElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Timing checks with specparam declarations elaborate
TEST(ElabA705, TimingChecksWithSpecparamsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSetup = 10;\n"
      "    $setup(d, posedge clk, tSetup);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.1 $setup_timing_check — command structure
// =============================================================================
TEST(ElabA70501, SetupWithNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — specify_terminal_descriptor with ranges
// =============================================================================
// Terminal with bit select elaborates
TEST(ElabA70503, TerminalBitSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data[0], posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// timing_check_event with posedge elaborates
TEST(ElabA70503, TimingCheckEventPosedgeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — timing_check_event with edge controls
// =============================================================================
// timing_check_event with no edge elaborates
TEST(ElabA70503, TimingCheckEventNoEdgeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
