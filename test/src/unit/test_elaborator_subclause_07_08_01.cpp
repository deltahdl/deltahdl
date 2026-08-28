#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DeclarationRangeParsing, AssocDimElaboratesWildcard) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [*]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
}

TEST(DeclarationRangeParsing, WildcardIndexWidth32) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [*]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_EQ(v.assoc_index_width, 32u);
}

TEST(DeclarationRangeParsing, WildcardNotStringIndex) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [*]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_FALSE(v.is_string_index);
}

// §7.8.1 — a wildcard-indexed associative array may not be used in a foreach
// loop.
TEST(WildcardIndexType, ForeachOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial foreach (aa[i]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wildcard associative array 'aa' may not be used "
                            "in a foreach loop",
                            3, "7.8.1"));
}

// Contrast: a foreach over a non-wildcard array elaborates cleanly, confirming
// the prohibition is specific to the wildcard index type.
TEST(WildcardIndexType, ForeachOnFixedArrayIsAllowed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int arr[4];\n"
      "  initial foreach (arr[i]) ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §7.8.1 — an array-locator method that returns index values (find_index) is
// not allowed on a wildcard-indexed associative array.
TEST(WildcardIndexType, FindIndexOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.find_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'find_index' is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

// §7.8.1 — find_first_index also returns indices and is rejected on a wildcard
// associative array.
TEST(WildcardIndexType, FindFirstIndexOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.find_first_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'find_first_index' is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

// §7.8.1 — likewise find_last_index is rejected on a wildcard associative
// array.
TEST(WildcardIndexType, FindLastIndexOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.find_last_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'find_last_index' is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

// §7.8.1 — a nonintegral index value is illegal; a real-literal index on a
// wildcard array is rejected.
TEST(WildcardIndexType, NonintegralIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial aa[1.5] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nonintegral index is not allowed on wildcard "
                            "associative array 'aa'",
                            3, "7.8.1"));
}

// §7.8.1 — the nonintegral prohibition also covers a real-typed variable used
// as the index, not just a real literal.
TEST(WildcardIndexType, RealVariableIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  real r;\n"
      "  initial aa[r] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nonintegral index is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

// §7.8.1 — the nonintegral prohibition covers every real-valued type. A
// shortreal-typed variable used as the index is rejected.
TEST(WildcardIndexType, ShortrealVariableIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  shortreal sr;\n"
      "  initial aa[sr] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nonintegral index is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

// §7.8.1 — likewise a realtime-typed variable is nonintegral and rejected as a
// wildcard index.
TEST(WildcardIndexType, RealtimeVariableIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  realtime rt;\n"
      "  initial aa[rt] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nonintegral index is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

// §7.8.1 — unique_index returns an array of index values, so like the other
// index-returning locators it is not allowed on a wildcard associative array.
TEST(WildcardIndexType, UniqueIndexOnWildcardIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int idx[$];\n"
      "  initial idx = aa.unique_index with (item > 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'unique_index' is not allowed on wildcard "
                            "associative array 'aa'",
                            4, "7.8.1"));
}

// Contrast: an integral index on the same wildcard array elaborates cleanly.
TEST(WildcardIndexType, IntegralIndexIsAllowed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial aa[3] = 0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §7.8.1 bars a wildcard-indexed associative array from a foreach loop, from
// the §7.12 methods that return an index, and from a nonintegral index, and it
// conditions none of the three on the statement the array is written in.
// WalkStmtsForWildcardTraversal wrote out six of the thirteen statement links
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h states, so
// each source below elaborated clean. The seven cases cover the seven links the
// walk did not read.
//
// Stmt::for_inits and Stmt::for_steps get the nonintegral-index form rather
// than the foreach form: A.6.8 admits only a list_of_variable_assignments or a
// for_variable_declaration at the initialization and only an
// operator_assignment, an inc_or_dec_expression or a function_subroutine_call
// at the step, so no loop_statement can be written at either, while a select
// with a real index is an ordinary expression that can.
TEST(WildcardIndexType, ForeachOnWildcardInForkArmIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial begin\n"
      "    fork\n"
      "      foreach (aa[i]) ;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wildcard associative array 'aa' may not be used "
                            "in a foreach loop",
                            5, "7.8.1"));
}

TEST(WildcardIndexType, NonintegralIndexInForInitIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int x;\n"
      "  integer i;\n"
      "  initial for (x = aa[1.5]; i < 0; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nonintegral index is not allowed on wildcard "
                            "associative array 'aa'",
                            5, "7.8.1"));
}

TEST(WildcardIndexType, NonintegralIndexInForStepIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  int x;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 0; x = aa[1.5]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nonintegral index is not allowed on wildcard "
                            "associative array 'aa'",
                            5, "7.8.1"));
}

// A.6.10 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, which is Stmt::assert_pass_stmt here and
// Stmt::assert_fail_stmt below.
TEST(WildcardIndexType, ForeachOnWildcardInAssertPassIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial assert (1) foreach (aa[i]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wildcard associative array 'aa' may not be used "
                            "in a foreach loop",
                            3, "7.8.1"));
}

TEST(WildcardIndexType, ForeachOnWildcardInAssertFailIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial assert (1) else foreach (aa[i]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wildcard associative array 'aa' may not be used "
                            "in a foreach loop",
                            3, "7.8.1"));
}

// §18.16 and A.6.7 give `randcase_item ::= expression : statement_or_null`.
TEST(WildcardIndexType, ForeachOnWildcardInRandcaseItemIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: foreach (aa[i]) ;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wildcard associative array 'aa' may not be used "
                            "in a foreach loop",
                            5, "7.8.1"));
}

// §18.17 and A.6.12 give `rs_code_block ::= { { data_declaration } {
// statement_or_null } }`.
TEST(WildcardIndexType, ForeachOnWildcardInRandsequenceCodeBlockIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int aa[*];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { foreach (aa[i]) ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wildcard associative array 'aa' may not be used "
                            "in a foreach loop",
                            5, "7.8.1"));
}

}  // namespace
