#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(HoldTimingCheckElaboration, ZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk, data, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(HoldTimingCheckElaboration, NegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk, data, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$hold timing check limit must be a non-negative "
                            "constant expression",
                            3, "31.3.2"));
}

TEST(HoldTimingCheckElaboration, NegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tHold = -3;\n"
      "    $hold(posedge clk, data, tHold);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$hold timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.3.2"));
}

TEST(HoldTimingCheckElaboration, NonNegativeSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tHold = 4;\n"
      "    $hold(posedge clk, data, tHold);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(HoldTimingCheckElaboration, NonNegativeArithmeticLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tHold = 3;\n"
      "    $hold(posedge clk, data, tHold + 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(HoldTimingCheckElaboration, NegativeArithmeticLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tHold = 3;\n"
      "    $hold(posedge clk, data, tHold - 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$hold timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.3.2"));
}

}  // namespace
