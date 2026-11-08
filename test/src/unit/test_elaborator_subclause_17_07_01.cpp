#include <gtest/gtest.h>

#include "fixture_checker_elab.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CheckerElab, ElaborateCheckerWithVars) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker my_chk;\n"
      "  logic [7:0] count;\n"
      "  assign count = 8'hFF;\n"
      "endchecker\n",
      f, "my_chk");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->name, "my_chk");
  EXPECT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->assigns.empty());
}

TEST(CheckerVariableAssignment, BlockingAssignmentToCheckerVariableElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic b);\n"
      "  logic c;\n"
      "  always_comb c = a & b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariableAssignment, AssignmentToCheckerVariableInInitialRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit v;\n"
      "  initial v = 1'b0;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "checker variable 'v' cannot be assigned in an initial procedure", 3,
      "17.7.1"));
}

TEST(CheckerVariableAssignment, AlwaysFfBlockingAssignmentRejectedInSource) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always_ff @(posedge clk) q = d;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a blocking assignment cannot appear in an "
                            "always_ff procedure of checker 'chk'",
                            3, "17.7.1"));
}

TEST(CheckerVariableAssignment, AlwaysFfNonblockingAssignmentElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariableAssignment, HierarchicalWriteOfCheckerVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit a;\n"
      "endchecker\n"
      "module m(input logic clk, input logic y);\n"
      "  chk my_check();\n"
      "  always @(posedge clk) my_check.a = y;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference into a checker is not permitted", 6, "23.6"));
}

TEST(CheckerVariableAssignment, HierarchicalReadOfCheckerVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit a;\n"
      "endchecker\n"
      "module m;\n"
      "  chk my_check();\n"
      "  logic x;\n"
      "  assign x = my_check.a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference into a checker is not permitted", 7, "23.6"));
}

TEST(CheckerVariableAssignment, HierarchicalReadInADeclarationRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit a;\n"
      "endchecker\n"
      "module m;\n"
      "  chk my_check();\n"
      "  wire x = my_check.a;\n"
      "  logic y = my_check.a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference into a checker is not permitted", 6, "23.6"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference into a checker is not permitted", 7, "23.6"));
}

TEST(CheckerVariableAssignment,
     HierarchicalContinuousWriteOfCheckerVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit a;\n"
      "endchecker\n"
      "module m(input logic y);\n"
      "  chk my_check();\n"
      "  assign my_check.a = y;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference into a checker is not permitted", 6, "23.6"));
}

TEST(CheckerVariableAssignment, ContinuousAssignmentToFreeVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, input logic a, input logic b);\n"
      "  rand bit x;\n"
      "  assign x = a & b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a continuous assignment cannot target free checker variable 'x'", 3,
      "17.7.1"));
}

TEST(CheckerVariableAssignment, BlockingAssignmentToFreeVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic b);\n"
      "  rand bit x;\n"
      "  always_comb x = a & b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a blocking assignment cannot target free checker variable 'x'", 3,
      "17.7.1"));
}

TEST(CheckerVariableAssignment,
     BlockingAssignmentToFreeVariableInLatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic en, input logic a);\n"
      "  rand bit x;\n"
      "  always_latch if (en) x = a;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a blocking assignment cannot target free checker variable 'x'", 3,
      "17.7.1"));
}

TEST(CheckerVariableAssignment, NonblockingAssignmentToFreeVariableElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  rand bit a;\n"
      "  always_ff @(posedge clk) a <= !a;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariableAssignment, DeclarationInitializerElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit w = 1'b0;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariableAssignment, RhsSequenceTriggeredElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, input logic a);\n"
      "  logic cv;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  always_ff @(posedge clk) cv <= s.triggered;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariableAssignment,
     CheckerVarAssignedInAnAssertionPassStatementOfAnInitialRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit v;\n"
      "  logic ready;\n"
      "  initial assert (ready) v = 1'b1;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "checker variable 'v' cannot be assigned in an initial procedure", 4,
      "17.7.1"));
}

TEST(CheckerVariableAssignment,
     CheckerVarAssignedInAnAssertionFailStatementOfAnInitialRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit held;\n"
      "  logic armed;\n"
      "  initial assert (armed) else held = 1'b0;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "checker variable 'held' cannot be assigned in an initial procedure", 4,
      "17.7.1"));
}

TEST(CheckerVariableAssignment,
     BlockingAssignmentToFreeVariableInAForInitializerRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a);\n"
      "  rand bit x;\n"
      "  int i;\n"
      "  always_comb\n"
      "    for (x = a; i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a blocking assignment cannot target free checker variable 'x'", 5,
      "17.7.1"));
}

TEST(CheckerVariableAssignment,
     BlockingAssignmentToFreeVariableInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic ok);\n"
      "  rand bit x;\n"
      "  always_comb assert (ok) x = a;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a blocking assignment cannot target free checker variable 'x'", 3,
      "17.7.1"));
}

TEST(CheckerVariableAssignment,
     BlockingAssignmentToFreeVariableInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic armed);\n"
      "  rand bit held;\n"
      "  always_comb assert (armed) else held = a;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a blocking assignment cannot target free checker variable 'held'", 3,
      "17.7.1"));
}

TEST(CheckerVariableAssignment,
     ABlockLocalOfAFreeVariableNameIsNotAFreeVariableAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic a, input logic b);\n"
      "  rand bit x;\n"
      "  always_comb begin\n"
      "    bit x;\n"
      "    x = a & b;\n"
      "  end\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariableAssignment,
     ABlockingAssignmentToAFreeVariableWithNoShadowingDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic b);\n"
      "  rand bit x;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "  end\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a blocking assignment cannot target free checker variable 'x'", 4,
      "17.7.1"));
}

}  // namespace
