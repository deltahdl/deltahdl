// Annex A.7.5.1: System timing check commands

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 All 12 commands with full argument forms
// =============================================================================
TEST(ElabA70501, AllTwelveCommandFormsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10, ntfr);\n"
      "    $hold(posedge clk, d, 5, ntfr);\n"
      "    $setuphold(posedge clk, d, 10, 5, ntfr, , , dCLK, dDATA);\n"
      "    $recovery(posedge clk, rst, 8, ntfr);\n"
      "    $removal(posedge clk, rst, 3, ntfr);\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
      "    $skew(posedge clk1, negedge clk2, 3, ntfr);\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr, 1, 0);\n"
      "    $period(posedge clk, 50, ntfr);\n"
      "    $width(posedge clk, 20, 1, ntfr);\n"
      "    $nochange(posedge clk, d, 0, 0, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
