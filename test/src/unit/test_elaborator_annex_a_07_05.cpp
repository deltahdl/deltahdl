#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimingCheckFlagElaboration, ConstantFlagsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter EB = 1) (input clk1, clk2);\n"
      "  localparam RA = 0;\n"
      "  specparam sp_ra = 1;\n"
      "  specify\n"
      "    specparam sp_eb = 0;\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, , EB, RA);\n"
      "    $fullskew(posedge clk1, posedge clk2, 5, 6, , sp_eb, sp_ra);\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, , EB + 1, 0:1:2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckFlagElaboration, TimeskewVariableEventBasedFlagIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clk1, clk2);\n"
      "  reg en;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, , en);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$timeskew event_based_flag is not a constant expression", 4, "31.4.2"));
}

TEST(TimingCheckFlagElaboration, TimeskewNetRemainActiveFlagIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clk1, clk2);\n"
      "  wire act;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, , 1, act);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$timeskew remain_active_flag is not a constant expression",
                    4, "31.4.2"));
}

TEST(TimingCheckFlagElaboration, FullskewVariableFlagsAreRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clk1, clk2);\n"
      "  reg en, act;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, posedge clk2, 5, 6, , en | 1, act:1:2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$fullskew event_based_flag is not a constant expression", 4, "31.4.3"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$fullskew remain_active_flag is not a constant expression",
                    4, "31.4.3"));
}

}  // namespace
