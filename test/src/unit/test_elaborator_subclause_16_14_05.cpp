#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §16.14.5: a concurrent assertion statement can be used outside a procedural
// context — directly within a module — so it elaborates as a module item.
// Each statement here writes its clocking event, §16.16 having one written
// with none take the default clocking or, with none in scope, be illegal.
TEST(AssertionStatementElaboration, AssertPropertyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  assert property (@(posedge clk) 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: a static concurrent assertion has always semantics, which the
// elaborator models on an always_ff process, but its clocking event is any
// event expression §16.5 allows, so one over a signal with no edge draws no
// §9.2.2.4 warning about sequential logic.
TEST(AssertionStatementElaboration,
     AClockingEventWithoutAnEdgeDrawsNoAlwaysFfWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clkev, a;\n"
      "  assert property (@(clkev) a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §16.14.5: the same statement can be used within an interface, again outside
// any procedural context, so it elaborates as an interface item.
TEST(AssertionStatementElaboration, AssertPropertyElaboratesInInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  logic clk;\n"
      "  assert property (@(posedge clk) 1);\n"
      "endinterface\n",
      f, "intf");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: the same statement can be used within a program, again outside any
// procedural context, so it elaborates as a program item.
TEST(AssertionStatementElaboration, AssertPropertyElaboratesInProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  logic clk;\n"
      "  assert property (@(posedge clk) 1);\n"
      "endprogram\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: a cover statement is likewise a concurrent assertion statement, so
// it too can appear outside procedural code — here directly within a module.
TEST(AssertionStatementElaboration, CoverPropertyElaboratesOutsideProcedure) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  cover property (@(posedge clk) 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: an assume statement is one of the concurrent assertion statement
// kinds that may appear outside procedural code, so it elaborates as a module
// item.
TEST(AssertionStatementElaboration, AssumePropertyElaboratesOutsideProcedure) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  assume property (@(posedge clk) 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: a restrict statement is the remaining concurrent assertion
// statement kind that may appear outside procedural code, so it too elaborates
// as a module item.
TEST(AssertionStatementElaboration,
     RestrictPropertyElaboratesOutsideProcedure) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  restrict property (@(posedge clk) 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: an assume statement, like the other concurrent assertion kinds, may
// appear in any of the three named non-procedural contexts, so it elaborates as
// an interface item.
TEST(AssertionStatementElaboration, AssumePropertyElaboratesInInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  logic clk;\n"
      "  assume property (@(posedge clk) 1);\n"
      "endinterface\n",
      f, "intf");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: the same assume statement elaborates as a program item, the third
// non-procedural context §16.14.5 names.
TEST(AssertionStatementElaboration, AssumePropertyElaboratesInProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  logic clk;\n"
      "  assume property (@(posedge clk) 1);\n"
      "endprogram\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: a cover statement is also usable outside procedural code within an
// interface, so it elaborates as an interface item.
TEST(AssertionStatementElaboration, CoverPropertyElaboratesInInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  logic clk;\n"
      "  cover property (@(posedge clk) 1);\n"
      "endinterface\n",
      f, "intf");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: the same cover statement elaborates as a program item.
TEST(AssertionStatementElaboration, CoverPropertyElaboratesInProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  logic clk;\n"
      "  cover property (@(posedge clk) 1);\n"
      "endprogram\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: a restrict statement, the remaining concurrent assertion kind, may
// likewise appear within an interface, so it elaborates as an interface item.
TEST(AssertionStatementElaboration, RestrictPropertyElaboratesInInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  logic clk;\n"
      "  restrict property (@(posedge clk) 1);\n"
      "endinterface\n",
      f, "intf");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: the same restrict statement elaborates as a program item,
// completing the four-kind by three-context grid of non-procedural placements.
TEST(AssertionStatementElaboration, RestrictPropertyElaboratesInProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  logic clk;\n"
      "  restrict property (@(posedge clk) 1);\n"
      "endprogram\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: the bare `assert property (ps) action_block` outside procedural
// code is equivalent to the explicit `always assert property (ps)
// action_block;` form, so the explicit form elaborates just as the bare one
// does.
TEST(AssertionStatementElaboration,
     AlwaysAssertPropertyEquivalentFormElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: likewise the bare `cover property (ps) statement_or_null` is
// equivalent to the explicit `always cover property (ps) statement_or_null`
// form, which therefore elaborates as well.
TEST(AssertionStatementElaboration,
     AlwaysCoverPropertyEquivalentFormElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  always cover property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
