#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimingCheckEventDefElaboration, PeriodElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $period(posedge clk, 50);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Table 31-11 accepting boundary: a zero limit sits at the non-negative edge
// and must be admitted -- the same fold path the negative-limit rejection tests
// below exercise.
TEST(TimingCheckEventDefElaboration, PeriodZeroLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $period(posedge clk, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Table 31-11 accepting side, specparam constant form (11.2.1): a limit written
// as a specparam that folds to a non-negative value is admitted. Built from
// real specparam declaration syntax so the value flows through elaboration.
TEST(TimingCheckEventDefElaboration, PeriodSpecparamLimitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam lim = 50;\n"
      "    $period(posedge clk, lim);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Table 31-11: the limit is a non-negative constant expression. A negative
// literal in the limit position folds to a negative constant and is rejected.
TEST(TimingCheckEventDefElaboration, PeriodNegativeLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $period(posedge clk, -50);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$period timing check limit must be a non-negative constant expression",
      3, "31.4.5"));
}

// The rule catches negativity after constant folding, not only on a bare
// literal: a specparam limit that folds below zero is rejected. Built from real
// specparam syntax so the value flows through elaboration, not a stub.
TEST(TimingCheckEventDefElaboration, PeriodNegativeSpecparamLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam lim = -50;\n"
      "    $period(posedge clk, lim);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$period timing check limit must be a non-negative constant expression",
      4, "31.4.5"));
}

// Table 31-11, constant-expression input form: a limit written as constant
// arithmetic over literals that folds below zero is rejected through the same
// folding path. This exercises the arithmetic constant form the limit may take.
TEST(TimingCheckEventDefElaboration, PeriodNegativeBinaryExprLimitRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $period(posedge clk, 5 - 60);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$period timing check limit must be a non-negative constant expression",
      3, "31.4.5"));
}

// End-to-end over the §31.5 edge-control-specifier dependency: the reference
// event is built from real edge[...] descriptor syntax and driven through the
// full parse+elaborate pipeline. An edge[...] descriptor is an edge
// specification, so $period's edge-required reference rule accepts it and the
// design elaborates cleanly.
TEST(TimingCheckEventDefElaboration, PeriodEdgeControlSpecifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $period(edge[01, 10] clk, 50);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// End-to-end over the §31.6 notifier dependency: the notifier argument is a
// module variable built from a real reg declaration, and the full $period form
// carrying it drives through parse+elaborate without error.
TEST(TimingCheckEventDefElaboration, PeriodDeclaredNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg nt;\n"
      "  specify\n"
      "    $period(posedge clk, 50, nt);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
