#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DefaultClockingElab, DuplicateDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb1 @(posedge clk1);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb2 @(posedge clk2);\n"
      "    input b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
