#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DefaultClockingElab, DuplicateDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk1, clk2;\n"
      "  logic a; default clocking cb1 @(posedge clk1);\n"
      "    input a;\n"
      "  endclocking\n"
      "  logic b; default clocking cb2 @(posedge clk2);\n"
      "    input b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one default clocking block is allowed per "
                            "scope",
                            5, "14.12"));
}

// §14.12: the clocking_identifier in a "default clocking <id>;" assignment
// statement shall be the name of a clocking block declared in scope.
TEST(DefaultClockingElab, AssignExistingClockingBlockOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.12: assigning a default clocking by a name that does not designate any
// clocking block is a compiler error.
TEST(DefaultClockingElab, AssignUnknownClockingBlockErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default clocking \"cb\" does not name a clocking "
                            "block",
                            2, "14.12"));
}

// §14.12 (claim B edge): the assignment-form identifier must name a clocking
// block specifically; naming an unrelated signal of the same name is an error.
TEST(DefaultClockingElab, AssignNonClockingEntityErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic cb;\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default clocking \"cb\" does not name a clocking "
                            "block",
                            3, "14.12"));
}

// §14.12 (claim C boundary): exactly one default clocking in a scope is legal
// and shall not raise a duplicate-default error.
TEST(DefaultClockingElab, SingleDefaultClockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.12 (claim C): specifying the default clocking more than once via the
// assignment form is also a compiler error, not only via inline declarations.
TEST(DefaultClockingElab, DuplicateDefaultClockingViaAssignmentErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one default clocking block is allowed per "
                            "scope",
                            8, "14.12"));
}

// §14.12 (claim E, mixed forms): the rule allowing a scope one default clocking
// spans both spellings of a default. An inline default clocking declaration and
// a later "default clocking <id>;" assignment together specify the default
// twice in the same module and shall be a compiler error, even though the
// assignment's identifier does name a real clocking block.
TEST(DefaultClockingElab, DuplicateDefaultViaMixedInlineAndAssignmentErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one default clocking block is allowed per "
                            "scope",
                            7, "14.12"));
}

// §14.12's Example 2: a nested module names, as its default clocking, a
// clocking block its enclosing module declares. A name no enclosing module
// declares as a clocking block is still reported.
TEST(DefaultClockingElab, NestedModuleNamesEnclosingClockingBlock) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module processor;\n"
             "  logic clk1;\n"
             "  clocking busA @(posedge clk1); endclocking\n"
             "  module cpu;\n"
             "    default clocking busA;\n"
             "    initial ##5 $display(\"x\");\n"
             "  endmodule\n"
             "  module bad;\n"
             "    default clocking nosuch;\n"
             "  endmodule\n"
             "  cpu u();\n"
             "  bad b();\n"
             "endmodule\n",
             f));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "default clocking \"busA\" does not name", 5,
                             "14.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default clocking \"nosuch\" does not name", 9,
                            "14.12"));
}

}  // namespace
