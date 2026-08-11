#include "fixture_elaborator.h"

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

// Table 31-10 accepting side: a zero limit and zero threshold sit at the
// non-negative boundary and must be admitted (a boundary the negative-limit
// rejection tests below share their fold path with).
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

// Table 31-10: the limit is a non-negative constant expression. A negative
// literal in the limit position folds to a negative constant and is rejected.
TEST(TimingCheckCommandElaboration, WidthNegativeLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, -20, 1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Table 31-10: the threshold is a distinct argument position and it too must be
// non-negative. A negative threshold is rejected even when the limit is valid.
TEST(TimingCheckCommandElaboration, WidthNegativeThresholdRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, 20, -1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The rule catches negativity after constant folding, not only on a bare
// literal: a specparam limit that folds below zero is rejected. The input is
// built from real specparam syntax so the value flows through elaboration.
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
  EXPECT_TRUE(f.has_errors);
}

// Table 31-10, constant-expression input form: a limit written as constant
// arithmetic over literals that folds below zero is rejected through the same
// folding path (its operands are literals, so only the sign check can reject
// it). This exercises the arithmetic constant form the limit may legally take.
TEST(TimingCheckCommandElaboration, WidthNegativeBinaryExprLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, 2 - 9, 1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Table 31-10, specparam input form in the threshold position: the threshold is
// its own §31.4.4 argument slot, and a specparam whose value folds below zero
// is rejected there just as in the limit position. Built from real specparam
// declaration syntax so the value flows through elaboration, not a stub.
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
  EXPECT_TRUE(f.has_errors);
}

// End-to-end over the §31.6 notifier dependency: the notifier argument is a
// declared module variable, and the $width threshold-then-notifier arrangement
// accepts it. The notifier is built from a real reg declaration and the full
// form drives through elaboration cleanly.
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

// §31.4.4: the report that refuses a negative $width limit names the subclause
// the check is stated in. The non-negative-limit pass runs once per timing
// check and each run names its own check's subclause, so this pins $width's
// rather than the subclause of whichever check ran first.
TEST(TimingCheckCommandElaboration, WidthNegativeLimitNames31_4_4) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, -20, 1);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "$width timing check limit must be a non-negative");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "31.4.4");
}

}  // namespace
