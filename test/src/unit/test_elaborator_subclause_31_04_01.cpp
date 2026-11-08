#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SystemTimingCheckElaboration, SkewZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, SkewNegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$skew timing check limit must be a non-negative "
                            "constant expression",
                            3, "31.4.1"));
}

TEST(SystemTimingCheckElaboration, SkewNegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = -3;\n"
      "    $skew(posedge clk1, negedge clk2, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$skew timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.4.1"));
}

TEST(SystemTimingCheckElaboration, SkewNonNegativeSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = 4;\n"
      "    $skew(posedge clk1, negedge clk2, tSkew);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SystemTimingCheckElaboration, SkewArithmeticLiteralLimitFoldsNegative) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $skew(posedge clk1, negedge clk2, 3 - 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$skew timing check limit must be a non-negative "
                            "constant expression",
                            3, "31.4.1"));
}

TEST(SystemTimingCheckElaboration, SkewSpecparamArithmeticLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSkew = 6;\n"
      "    $skew(posedge clk1, negedge clk2, tSkew - 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
