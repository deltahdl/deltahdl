#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// A checker body admits an initial procedure alongside a variable
// declaration. The variable takes its value from its declaration rather than
// from the procedure: §17.7.1 forbids assigning a checker variable in an
// initial procedure while allowing it an initializer in its declaration, and
// gives `bit v; initial v = 1'b0;` as illegal against `bit w = 1'b0;` as legal.
// This test previously used the illegal form.
TEST(CheckerProcedures, InitialProcedureBesideAnInitializedVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic flag = 0;\n"
      "  initial a0: assert (1);\n"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker variable 'flag' cannot be assigned in an "
                            "initial procedure",
                            3, "17.7.1"));
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
      "checker chk(input logic clk, input logic a, input logic b);\n"
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
      "  initial a0: assert (1);\n"
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

// A.1.8: a checker's items, checker_or_generate_item, reach no instantiation
// but a checker's, through assertion_item, and never the udp_instantiation
// only A.1.4's module_or_generate_item reaches. A UDP instance reads as a
// module instance until its name resolves, so it is the elaborator that
// reports one standing among a checker's items, under A.1.8 rather than §24.3,
// which keeps primitives out of a program (#7569).
TEST(CheckerOrGenerateItem, AUdpInstanceIsNoCheckerItem) {
  ElabFixture f;
  ElaborateSrc(
      "checker c(logic a, logic z);\n"
      "  inv u(z, a);\n"
      "endchecker\n"
      "primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; logic x, y; c k(x, y); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive cannot be instantiated inside checker "
                            "'c'",
                            2, "A.1.8"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "primitive cannot be instantiated inside checker "
                             "'c'",
                             2, "24.3"));
}

}  // namespace
