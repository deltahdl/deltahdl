#include "fixture_elaborator.h"

namespace {

// A checker body admits an initial procedure alongside a variable
// declaration. The variable takes its value from its declaration rather than
// from the procedure: §17.7.1 states that "a checker variable may not be
// assigned in an initial procedure, but may be initialized in its
// declaration", and gives `bit v; initial v = 1'b0;` as illegal against
// `bit w = 1'b0;` as legal. This test previously used the illegal form.
TEST(CheckerProcedures, InitialProcedureBesideAnInitializedVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic flag = 0;\n"
      "  initial $display(\"chk\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §17.7.1, the negative form of the same rule, so the diagnostic that enforces
// it is pinned rather than left to be deleted while chasing the tests above.
TEST(CheckerProcedures, CheckerVariableAssignedInInitialIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

TEST(CheckerProcedures, CheckerWithPortsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, output bit ok);\n"
      "  logic sig;\n"
      "  assign ok = sig;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerWithAssertionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerWithMultipleItemsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      // §17.7.1: initialized in its declaration, not assigned in the initial
      // procedure below, which the clause forbids for a checker variable.
      "  logic flag = 0;\n"
      "  initial $display(\"chk\");\n"
      // §17.5: a general 'always' procedure is not among the always forms
      // permitted in a checker (only always_comb/always_latch/always_ff);
      // a general always in a checker was removed in IEEE 1800-2023.
      "  always_ff @(posedge flag) flag <= ~flag;\n"
      "  final $display(\"done\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
