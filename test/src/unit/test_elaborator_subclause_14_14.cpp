#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(GlobalClockingElab, DuplicateGlobalClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m; logic clk1, clk2;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            3, "14.14"));
}

TEST(GlobalClockingElab, GlobalClockInEventControlWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  always @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            4, "14.14"));
}

TEST(GlobalClockingElab, DuplicateGlobalClockingInProgramErrors) {
  ElabFixture f;
  ElaborateSrc(
      "program p(input clk1, input clk2);\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endprogram\n",
      f, "p");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            3, "14.14"));
}

TEST(GlobalClockingElab, DuplicateGlobalClockingInCheckerErrors) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk1, input logic clk2);\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            3, "14.14"));
}

TEST(GlobalClockingElab, DuplicateGlobalClockingNames14_14) {
  ElabFixture f;
  ElaborateSrc(
      "module m; logic clk1, clk2;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only one global clocking block is allowed per scope", 3, "14.14"));
}

void InstanceProcessBodies(RtlirDesign* design, Stmt** first, Stmt** second) {
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2U);
  auto* u0 = top->children[0].resolved;
  auto* u1 = top->children[1].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_NE(u1, nullptr);
  ASSERT_EQ(u0->processes.size(), 1U);
  ASSERT_EQ(u1->processes.size(), 1U);
  *first = u0->processes[0].body;
  *second = u1->processes[0].body;
}

TEST(GlobalClockingElab,
     GlobalClockSubstitutionGivesEachInstanceItsOwnProcessBody) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  logic clk, done;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial @($global_clock) done = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  sub u0();\n"
      "  sub u1();\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  Stmt* first = nullptr;
  Stmt* second = nullptr;
  InstanceProcessBodies(design, &first, &second);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_NE(first, second)
      << "both instances of sub hold one body statement, so the §14.14 "
         "substitution made for either of them was written into the other";
}

TEST(GlobalClockingElab, ProcessBodyWithNoGlobalClockIsSharedBetweenInstances) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  logic clk, done;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  initial done = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  sub u0();\n"
      "  sub u1();\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  Stmt* first = nullptr;
  Stmt* second = nullptr;
  InstanceProcessBodies(design, &first, &second);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first, second)
      << "a body naming no $global_clock was copied per instance, so every "
         "process body is allocated again for every instantiation";
}

TEST(GlobalClockingElab, GlobalClockInAForkStatementWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial fork\n"
      "    @($global_clock) x = 1'b1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            4, "14.14"));
}

TEST(GlobalClockingElab, GlobalClockInAForInitializerWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = $global_clock; i < 1; i = i + 1)\n"
      "      x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            5, "14.14"));
}

TEST(GlobalClockingElab, GlobalClockInAForStepWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; i = $global_clock)\n"
      "      x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            5, "14.14"));
}

TEST(GlobalClockingElab,
     GlobalClockInAnAssertionPassStatementWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x, ok;\n"
      "  initial assert (ok) @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
}

TEST(GlobalClockingElab,
     GlobalClockInAnAssertionFailStatementWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x, ok;\n"
      "  initial assert (ok) else @($global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
}

TEST(GlobalClockingElab, GlobalClockInARandcaseItemWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial randcase 1: @($global_clock) x = 1'b1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
}

TEST(GlobalClockingElab,
     GlobalClockInARandsequenceCodeBlockWithoutDeclarationErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { @($global_clock) x = 1'b1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            5, "14.14"));
}

TEST(GlobalClockingElab, GlobalClockInAnAlwaysIffConditionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic x;\n"
      "  always @(posedge clk iff $global_clock) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration",
                            4, "14.14"));
}

}  // namespace
