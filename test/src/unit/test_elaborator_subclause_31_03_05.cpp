#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RecoveryTimingCheckElaboration, ZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recovery(posedge rst, clk, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecoveryTimingCheckElaboration, NegativeLiteralLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recovery(posedge rst, clk, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$recovery timing check limit must be a "
                            "non-negative constant expression",
                            3, "31.3.5"));
}

TEST(RecoveryTimingCheckElaboration, NegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = -3;\n"
      "    $recovery(posedge rst, clk, tRec);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$recovery timing check limit must be a "
                            "non-negative constant expression",
                            4, "31.3.5"));
}

TEST(RecoveryTimingCheckElaboration, NonNegativeSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = 4;\n"
      "    $recovery(posedge rst, clk, tRec);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecoveryTimingCheckElaboration, NonNegativeArithmeticLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = 3;\n"
      "    $recovery(posedge rst, clk, tRec + 2);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RecoveryTimingCheckElaboration, NegativeArithmeticLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRec = 3;\n"
      "    $recovery(posedge rst, clk, tRec - 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$recovery timing check limit must be a "
                            "non-negative constant expression",
                            4, "31.3.5"));
}

}  // namespace
