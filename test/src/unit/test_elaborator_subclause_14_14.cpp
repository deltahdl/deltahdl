#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$global_clock has no effective global clocking "
                            "declaration in any enclosing scope up to the "
                            "top-level hierarchy block",
                            3, "14.14"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            4, "14.14"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            3, "14.14"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            3, "14.14"));
}

// §14.14: the report that refuses a second global clocking declaration names
// the subclause stating the rule ("A given module, interface, checker, or
// program shall contain at most one global clocking declaration").
TEST(GlobalClockingElab, DuplicateGlobalClockingNames14_14) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only one global clocking block is allowed per scope", 3, "14.14"));
}

// The body statement of the one process each of the two instances the top
// module holds was elaborated into. The two cases below differ in the source
// they elaborate and in what they claim about the pair, so the walk from the
// design down to the two RtlirProcess::body pointers is written once here.
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

// §14.14: an event control naming $global_clock waits on the event expression
// of the effective global clocking declaration, so BuildProcessBody in
// src/elaborator/elaborator_process.cpp rewrites the event control the
// procedure body holds. The body it rewrites is reached through the one
// ModuleDecl the parser built, and Elaborator::ElaborateModule runs once per
// instantiation, so a rewrite made in place is written into the statement
// every instance of the module shares. This fails when the two instances of
// `sub` name one Stmt.
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

// §14.14: a procedure body naming no $global_clock has nothing to substitute,
// so SubstituteGlobalClockEventControls in
// src/elaborator/global_clock_assertion_event.cpp returns the statement it was
// given rather than a copy of it. Both instances of `sub` then hold the one
// Stmt the parser built for the module, which is what the elaborator does with
// every process body it does not rewrite. This fails when a body is copied per
// instance whether anything in it was rewritten or not.
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

}  // namespace
