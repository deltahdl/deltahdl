#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §16.14.5: a concurrent assertion statement can be used outside a procedural
// context — directly within a module — so it elaborates as a module item.
TEST(AssertionStatementElaboration, AssertPropertyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  assert property (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.14.5: the same statement can be used within an interface, again outside
// any procedural context, so it elaborates as an interface item.
TEST(AssertionStatementElaboration, AssertPropertyElaboratesInInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  assert property (1);\n"
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
      "  assert property (1);\n"
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
      "  cover property (1);\n"
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
      "  assume property (1);\n"
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
      "  restrict property (1);\n"
      "endmodule\n",
      f);
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
