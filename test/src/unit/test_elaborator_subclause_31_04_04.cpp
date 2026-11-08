#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandElaboration, WidthBasicElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, 20);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckCommandElaboration, WidthWithSpecparamsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam lim = 20;\n"
      "    specparam thr = 1;\n"
      "    $width(posedge clk, lim, thr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckCommandElaboration, WidthZeroLimitAndThresholdElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, 0, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckCommandElaboration, WidthNegativeLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, -20, 1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$width timing check limit must be a non-negative constant expression", 3,
      "31.4.4"));
}

TEST(TimingCheckCommandElaboration, WidthNegativeThresholdRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, 20, -1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$width timing check limit must be a non-negative constant expression", 3,
      "31.4.4"));
}

TEST(TimingCheckCommandElaboration, WidthNegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam lim = -20;\n"
      "    $width(posedge clk, lim, 1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$width timing check limit must be a non-negative constant expression", 4,
      "31.4.4"));
}

TEST(TimingCheckCommandElaboration, WidthNegativeBinaryExprLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, 2 - 9, 1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$width timing check limit must be a non-negative constant expression", 3,
      "31.4.4"));
}

TEST(TimingCheckCommandElaboration, WidthNegativeSpecparamThresholdRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam thr = -5;\n"
      "    $width(posedge clk, 20, thr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$width timing check limit must be a non-negative constant expression", 4,
      "31.4.4"));
}

TEST(TimingCheckCommandElaboration, WidthDeclaredNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg nt;\n"
      "  specify\n"
      "    $width(posedge clk, 20, 5, nt);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimingCheckCommandElaboration, WidthNegativeLimitNames31_4_4) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, -20, 1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$width timing check limit must be a non-negative",
                            3, "31.4.4"));
}

}  // namespace
