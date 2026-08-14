#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

// Table 31-9 accepting side of the binary-arithmetic input form: a limit built
// as a binary expression of literals that folds to a non-negative value is
// admitted (the fold path is the same one the negative-binary test exercises,
// so this guards against a non-negative result being wrongly rejected).
TEST(SystemTimingCheckElaboration,
     FullskewNonNegativeBinaryExprLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, 3 + 4, 6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Table 31-9: limit1 must be a non-negative constant expression. A negative
// literal in the first limit position folds to a negative constant and is
// rejected.
TEST(SystemTimingCheckElaboration, FullskewNegativeFirstLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, -3, 6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$fullskew timing check limit must be a non-negative", 3, "31.4.3"));
}

// Table 31-9: limit2 is a distinct argument position unique to $fullskew (a
// two-limit check), and it too must be non-negative. A negative second limit is
// rejected even when the first limit is valid.
TEST(SystemTimingCheckElaboration, FullskewNegativeSecondLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, -6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$fullskew timing check limit must be a non-negative", 3, "31.4.3"));
}

// The rule catches negativity after constant folding, not only on a bare
// literal: a specparam limit that folds below zero is rejected in either limit
// position.
TEST(SystemTimingCheckElaboration, FullskewNegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tHi = -6;\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, tHi);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$fullskew timing check limit must be a non-negative", 4, "31.4.3"));
}

// A second limit built as a binary arithmetic expression that folds below zero
// is rejected through the folding path (its operands are literals, so only the
// sign check can reject it).
TEST(SystemTimingCheckElaboration, FullskewNegativeBinaryExprLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, 2 - 9);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$fullskew timing check limit must be a non-negative", 3, "31.4.3"));
}

}  // namespace
