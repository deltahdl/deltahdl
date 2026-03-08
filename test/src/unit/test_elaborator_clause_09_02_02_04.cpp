#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §9.2.2.4: always_ff with no event control produces an error.
TEST(ElabClause09_02_02_04, MissingEventControlErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q, d;\n"
      "  always_ff q <= d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.4: always_ff with blocking timing control in body produces an error.
TEST(ElabClause09_02_02_04, BlockingTimingControlInBodyErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) #5 q <= d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.4: always_ff with fork-join produces an error.
TEST(ElabClause09_02_02_04, ForkJoinInAlwaysFFErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always_ff @(posedge clk) begin\n"
      "    fork\n"
      "      a <= 1;\n"
      "      b <= 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.4: Valid always_ff with posedge clock, no errors.
TEST(ElabClause09_02_02_04, ValidPosedgeClockNoErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.2.2.4: always_ff elaborates to kAlwaysFF process kind.
TEST(ElabClause09_02_02_04, ElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) found = true;
  }
  EXPECT_TRUE(found);
}

// §9.2.2.4: always_ff sensitivity list is preserved (posedge clk or negedge rst).
TEST(ElabClause09_02_02_04, SensitivityListPreserved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst_n, d, q;\n"
      "  always_ff @(posedge clk or negedge rst_n)\n"
      "    if (!rst_n) q <= 0;\n"
      "    else q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& procs = design->top_modules[0]->processes;
  bool found = false;
  for (auto& p : procs) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) {
      found = true;
      EXPECT_EQ(p.sensitivity.size(), 2u);
      EXPECT_EQ(p.sensitivity[0].edge, Edge::kPosedge);
      EXPECT_EQ(p.sensitivity[1].edge, Edge::kNegedge);
    }
  }
  EXPECT_TRUE(found);
}

// §9.2.2.4: always_ff with no edge events warns about non-sequential logic.
TEST(ElabClause09_02_02_04, NoEdgeWarnsNotSequential) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §9.2.2.4: always_ff with posedge clock does not warn.
TEST(ElabClause09_02_02_04, PosedgeClockNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §9.2.2.4: Multi-driver: same variable in two always_ff blocks.
TEST(ElabClause09_02_02_04, MultiDriverTwoAlwaysFFErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, q;\n"
      "  always_ff @(posedge clk) q <= a;\n"
      "  always_ff @(posedge clk) q <= b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.4: Multi-driver: always_ff and continuous assignment.
TEST(ElabClause09_02_02_04, MultiDriverFFAndContAssignErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "  assign q = d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.4: Multi-driver: always_ff and always_comb same variable.
TEST(ElabClause09_02_02_04, MultiDriverFFAndCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "  always_comb q = d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.2.4: Different variables in separate always_ff blocks, no error.
TEST(ElabClause09_02_02_04, DifferentVarsInSeparateFFOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, q1, q2;\n"
      "  always_ff @(posedge clk) q1 <= a;\n"
      "  always_ff @(posedge clk) q2 <= b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.2: fork/join in always_ff is an error.
TEST(ElabClause09_03_02, ForkInAlwaysFFErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always_ff @(posedge clk) begin\n"
      "    fork\n"
      "      a <= 1;\n"
      "      b <= 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.6.1: Wait fork is a timing control, error in always_ff.
TEST(ElabClause09_06_01, WaitForkInAlwaysFFErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  always_ff @(posedge clk) begin\n"
      "    wait fork;\n"
      "    a <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
