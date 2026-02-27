// §31.2: Overview

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// All 12 system_timing_check alternatives in one specify block
TEST(ElabA705, AllTwelveCheckTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10);\n"
      "    $hold(posedge clk, d, 5);\n"
      "    $setuphold(posedge clk, d, 10, 5);\n"
      "    $recovery(posedge clk, rst, 8);\n"
      "    $removal(posedge clk, rst, 3);\n"
      "    $recrem(posedge clk, rst, 8, 3);\n"
      "    $skew(posedge clk1, negedge clk2, 3);\n"
      "    $timeskew(posedge clk1, posedge clk2, 5);\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, 6);\n"
      "    $period(posedge clk, 50);\n"
      "    $width(posedge clk, 20);\n"
      "    $nochange(posedge clk, d, 0, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
