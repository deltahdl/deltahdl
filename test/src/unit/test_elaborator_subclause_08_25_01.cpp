#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ParameterizedScopeResolutionElaboration,
     SpecificSpecializationAccessesTypeParamOk) {
  // The scope resolution operator reaches a type parameter of the class, not
  // only its value parameters. The explicit specialization supplies the actual
  // type that the parameter name resolves to, here giving the variable the
  // integer type.
  EXPECT_TRUE(
      ElabOk("class C #(type T = int);\n"
             "endclass\n"
             "module m;\n"
             "  C#(integer)::T x;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     BothClassAndLocalParamsAccessibleOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int a, b;\n"
             "  initial begin\n"
             "    a = C#()::p;\n"
             "    b = C#()::q;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     OutOfBlockMethodForParameterizedClassOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  extern static function int f();\n"
             "endclass\n"
             "function int C::f();\n"
             "  return p;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration, MultipleSpecializationsAccessOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int a, b;\n"
             "  initial begin\n"
             "    a = C#(3)::p;\n"
             "    b = C#(7)::p;\n"
             "  end\n"
             "endmodule\n"));
}

// The report stands at the unadorned prefix itself -- the site passes
// `e->lhs->range.start`, the `C` of `C::q`.
TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeOutsideIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInContAssignIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  assign result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInNestedExprIsError) {
  // The prohibition on the bare parameterized-class name as a scope resolution
  // prefix outside the class applies wherever the prefix appears, including as
  // a subexpression of a larger expression, not only as the whole right-hand
  // side.
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = 1 + C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInAlwaysCombIsError) {
  // The same prohibition holds across procedural contexts; an always_comb block
  // outside the class is still outside the class, so the unadorned prefix is
  // illegal there too.
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  always_comb result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeInsideClassOk) {
  // Within the parameterized class's own scope the unadorned name may prefix
  // the scope resolution operator to name a member; the restriction that makes
  // the bare name illegal applies only outside the class and its out-of-block
  // declarations. Here it names a member rather than the default
  // specialization.
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "  static function int g();\n"
             "    return C::q;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.25.1: the explicit specialization form denotes a specific parameter in a
// constant-expression position, so `C#(4)::p` initializing a localparam folds
// to 4 and not to the class default of 1. §27.4 makes a generate block "a
// separate scope and a new level of hierarchy when it is instantiated" and
// says nothing that would stop that at the boundary, so the same initializer
// written inside a block folds to the same 4. The class default is written 1
// so that a fold answering the default misses.
//
// This fails while Elaborator::ProcessPendingGenerate in
// src/elaborator/elaborator_generate.cpp opens no ParamClassRegistryGuard:
// SpecializedParamClass in src/elaborator/const_eval_func.cpp finds no
// registry, the access does not fold at all, and W is left unresolved.
TEST(ParameterizedScopeResolutionElaboration,
     SpecializationParameterFoldsInsideAGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 1);\n"
      "endclass\n"
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam int W = C#(4)::p;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* w = FindParam(design, "m", "W");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_resolved);
  EXPECT_EQ(w->resolved_value, 4);
}

// The seven cases below cover the child-statement links of Stmt that
// WalkStmtsForParamScope in src/elaborator/elaborator_validate_classes.cpp
// reaches for the first time now that it takes its list from ForEachChildStmt
// in src/elaborator/elaborator_validate_internal.h. It had written out six of
// the thirteen, so the unadorned prefix standing in any of the other seven
// reached CheckParamScopeExpr through no link and was left unreported. §8.25.1
// requires the explicit specialization wherever the prefix is written outside
// the class, and each case below is that one rule in one more statement
// position. The report stands at the prefix itself, the `C` of `C::q`.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, so a fork arm
// holds the expression like any other statement position.
TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeInForkArmIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial fork\n"
      "    result = C::q;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 7, "8.25.1"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`, so
// the right-hand side of a header assignment is an ordinary expression. The
// loop's control variable is declared above the loop, which leaves the header
// as the only place the prefix is written.
TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInForInitializationIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  int i;\n"
      "  initial for (result = C::q; i < 2; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 7, "8.25.1"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, so a for step carries an
// expression the same way.
TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeInForStepIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 2; result = C::q) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 7, "8.25.1"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// Whether the arm runs is settled when the design runs, and §8.25.1 is a rule
// about how the prefix is written.
TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInAssertionPassStmtIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial assert (1) result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInAssertionFailStmtIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial assert (1) else result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. The item is reported whether the weighted draw would select it or
// not.
TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInRandcaseItemIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : result = C::q;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 8, "8.25.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp
// puts them in RsProd::code_stmts, which Stmt::rs_productions reaches and no
// other member of Stmt does.
TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInRandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { result = C::q; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 8, "8.25.1"));
}

}  // namespace
