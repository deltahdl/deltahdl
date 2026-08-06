#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GlobalClockingElab, DuplicateGlobalClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(GlobalClockingElab, GlobalClockInEventControlWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(GlobalClockingElab, GlobalClockInEventControlWithDeclarationIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §14.14 lookup rule b): a $global_clock reference in a child that declares no
// global clocking of its own resolves against the parent instance's global
// clocking. This is the common_sub pattern from the clause example.
TEST(GlobalClockingElab, GlobalClockResolvesToParentInstanceDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  child c();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §14.14 rule b) climbs through more than one level of instantiation until a
// global clocking is found.
TEST(GlobalClockingElab, GlobalClockResolvesThroughTwoInstanceLevels) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l();\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  global clocking gc @(posedge clk); endclocking\n"
      "  mid m();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §14.14 rule b) error path: when the lookup reaches the top-level hierarchy
// block without finding a global clocking, the reference is an error even
// though it sits several levels below the top.
TEST(GlobalClockingElab,
     GlobalClockWithNoDeclarationAnywhereInHierarchyErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §14.14: the at-most-one-per-scope rule applies to every scope kind the clause
// enumerates, not just modules -- here two global clockings in one interface.
TEST(GlobalClockingElab, DuplicateGlobalClockingInInterfaceErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic clk1, clk2;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.14: the at-most-one rule also holds in a program scope. The program is
// named as the explicit top so its body is actually elaborated.
TEST(GlobalClockingElab, DuplicateGlobalClockingInProgramErrors) {
  ElabFixture f;
  ElaborateSrc(
      "program p(input clk1, input clk2);\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endprogram\n",
      f, "p");
  EXPECT_TRUE(f.has_errors);
}

// §14.14: and in a checker scope -- the fourth declared scope the clause
// enumerates. The checker is named as the explicit top so it is elaborated.
TEST(GlobalClockingElab, DuplicateGlobalClockingInCheckerErrors) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input clk1, input clk2);\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
