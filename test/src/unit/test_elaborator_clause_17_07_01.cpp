#include <gtest/gtest.h>

#include "fixture_checker_elab.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §17.7.1: a checker holding a non-free variable with a continuous assignment
// elaborates into a module carrying that variable and that assign.
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

// §17.7.1: a checker variable may be assigned by a blocking procedural
// assignment. A non-free checker variable driven by a blocking assignment in an
// always_comb procedure elaborates cleanly, exercising the blocking procedural
// form of the opening allowance. The continuous form is covered by
// ElaborateCheckerWithVars and the nonblocking form by
// AlwaysFfNonblockingAssignmentElaborates below.
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

// §17.7.1: a checker variable may not be assigned in an initial procedure. A
// checker variable target of a blocking assignment inside an initial procedure
// is rejected by the elaborator; the legal counterpart — initializing the same
// variable in its declaration — is covered by DeclarationInitializerElaborates
// below.
TEST(CheckerVariableAssignment, AssignmentToCheckerVariableInInitialRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit v;\n"
      "  initial v = 1'b0;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

// The tests below drive each enforced §17.7.1 rule through the real
// parse+elaborate pipeline, observing the production elaborator apply (or not
// apply) the rule to a checker built from real source.

// §17.7.1: in an always_ff procedure only nonblocking assignments are allowed.
// A blocking assignment to a checker variable in a checker always_ff procedure
// is rejected by the elaborator.
TEST(CheckerVariableAssignment, AlwaysFfBlockingAssignmentRejectedInSource) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, input logic d);\n"
      "  logic q;\n"
      "  always_ff @(posedge clk) q = d;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

// §17.7.1: the accepting side of the always_ff rule — the same procedure using
// a nonblocking assignment elaborates cleanly, isolating the blocking form as
// the cause of the rejection above.
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

// §17.7.1: referencing a checker variable through its hierarchical name in an
// assignment (§23.6) is illegal. A module that writes an instantiated checker's
// variable from a procedural assignment is rejected.
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
  EXPECT_TRUE(f.has_errors);
}

// §17.7.1: the continuous-assignment form of the same rule — reading an
// instantiated checker's variable through its hierarchical name on the
// right-hand side of a continuous assignment is likewise illegal.
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
  EXPECT_TRUE(f.has_errors);
}

// §17.7.1: the left-hand-side position of the same rule — targeting an
// instantiated checker's variable through its hierarchical name on the
// left-hand side of a continuous assignment is illegal, a distinct assignment
// position from the right-hand-side read above.
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
  EXPECT_TRUE(f.has_errors);
}

// §17.7.1: a continuous assignment to a free (rand) checker variable is
// illegal. The free variable `x` driven by an `assign` is rejected by the
// elaborator.
TEST(CheckerVariableAssignment, ContinuousAssignmentToFreeVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, input logic a, input logic b);\n"
      "  rand bit x;\n"
      "  assign x = a & b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

// §17.7.1: a blocking procedural assignment to a free (rand) checker variable
// is illegal. The free variable `x` driven by a blocking assignment in an
// always_comb procedure — the illegal form the clause names — is rejected.
TEST(CheckerVariableAssignment, BlockingAssignmentToFreeVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic b);\n"
      "  rand bit x;\n"
      "  always_comb x = a & b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

// §17.7.1: the blocking-assignment prohibition on a free variable holds in any
// procedure, not only always_comb. A free variable assigned by a blocking
// assignment inside an always_latch procedure is rejected the same way.
TEST(CheckerVariableAssignment,
     BlockingAssignmentToFreeVariableInLatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic en, input logic a);\n"
      "  rand bit x;\n"
      "  always_latch if (en) x = a;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

// §17.7.1: the accepting side of the free-variable rule — a free checker
// variable driven by a nonblocking assignment in an always_ff procedure is the
// one legal form, and elaborates cleanly. This also covers the allowance that
// the left-hand side of a nonblocking assignment may hold a free checker
// variable (the toggling `a <= !a` pattern).
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

// §17.7.1: a checker variable may be initialized in its declaration. The
// declaration initializer — the legal counterpart to an assignment inside an
// initial procedure — elaborates cleanly.
TEST(CheckerVariableAssignment, DeclarationInitializerElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit w = 1'b0;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

// §17.7.1: the right-hand side of a checker variable assignment may contain the
// sequence method triggered (§16.13.6). A checker variable driven by a
// nonblocking assignment whose right-hand side reads a named sequence's
// triggered status elaborates cleanly, observing the allowance on real source
// built from §16.13.6's own syntax.
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

}  // namespace
