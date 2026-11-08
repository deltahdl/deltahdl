#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SetupTimingCheckElaboration, ZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SetupTimingCheckElaboration, NegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk);\n"
      "  reg n = 0;\n"
      "  specify\n"
      "    $setup(d, posedge clk, -5, n);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$setup timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.3.1"));
}

TEST(SetupTimingCheckElaboration, NegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    specparam tSU = -3;\n"
      "    $setup(d, posedge clk, tSU);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$setup timing check limit must be a non-negative "
                            "constant expression",
                            4, "31.3.1"));
}

TEST(SetupTimingCheckElaboration, NonNegativeSpecparamExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk);\n"
      "  specify\n"
      "    specparam tSU = 7;\n"
      "    $setup(d, posedge clk, tSU - 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
