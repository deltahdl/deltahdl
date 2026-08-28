#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §20.7.1: querying an inner variable-sized dimension is an error.
//
// For `int a[3][][5]`, dimension 1 is the fixed [3], dimension 2 is the dynamic
// [], and dimension 3 is the fixed [5]. Because each element of dimension 1 can
// hold a differently sized dynamic array, $size(a, 2) has no single answer and
// is an error, while the fixed dimensions 1 and 3 are fine. This mirrors the
// example in the LRM.

TEST(ArrayQueryVariableDim, SizeOfDynamicInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            4, "20.7.1"));
}

TEST(ArrayQueryVariableDim, SizeOfFixedFirstDimensionIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, 1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, SizeOfFixedInnerDimensionIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, 3);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The restriction is on n > 1: the slowest-varying dimension may be queried
// even when it is itself variable-sized (a plain queue is dimension 1).
TEST(ArrayQueryVariableDim, SizeOfQueueFirstDimensionIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int q[$];\n"
      "  int n;\n"
      "  initial n = $size(q, 1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// A queue nested under a fixed dimension is a variable-sized dimension 2.
TEST(ArrayQueryVariableDim, SizeOfQueueInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][$];\n"
      "  int n;\n"
      "  initial n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            4, "20.7.1"));
}

// A wildcard associative array nested under a fixed dimension is likewise a
// variable-sized dimension 2, so querying it is an error.
TEST(ArrayQueryVariableDim, SizeOfWildcardAssocInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][*];\n"
      "  int n;\n"
      "  initial n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            4, "20.7.1"));
}

// The LRM example only shows $size, but the restriction applies to every
// per-dimension query function ($left, $right, $low, $high, $increment, $size),
// which all route through the same recognizer. One non-$size function stands in
// for the whole set: $left rejecting an inner dynamic dimension confirms the
// rule is not tied to $size.
TEST(ArrayQueryVariableDim, LeftOfDynamicInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $left(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$left' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            4, "20.7.1"));
}

// The restriction fires wherever the query appears, not only in a procedural
// assignment. A variable declaration initializer is a distinct elaboration walk
// path (the initializer expression rather than a statement body); a variable
// initialized with $size on an inner dynamic dimension is rejected there too.
TEST(ArrayQueryVariableDim, InnerVariableDimInDeclInitializerIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            3, "20.7.1"));
}

// Control for the initializer-position case above: querying a fixed dimension
// from the same declaration-initializer position is legal, confirming the error
// there comes from the variable-sized rule and not from the initializer syntax.
TEST(ArrayQueryVariableDim, FixedDimInDeclInitializerIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n = $size(a, 3);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// The restriction is on a bare array variable. When the first argument resolves
// an outer dimension by indexing (here a[2], a single dynamic array), the query
// targets a well-defined object and is legal even at a dimension that is
// variable-sized for the parent array. This mirrors the $size(a[2], 1) case in
// the LRM example.
TEST(ArrayQueryVariableDim, IndexedElementQueryIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a[2], 1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.7 states the dimension argument is a constant expression, so the query
// index may be a parameter rather than a literal. Folding it must still surface
// the §20.7.1 error when it names an inner variable-sized dimension. Here the
// parameter value 2 selects the dynamic dimension of a[3][][5].
TEST(ArrayQueryVariableDim, ParameterDimensionIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter int D = 2;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, D);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            5, "20.7.1"));
}

// A localparam-valued dimension index that selects a fixed dimension is legal,
// confirming the folded index is compared against the real dimension list and
// not merely rejected for being non-literal.
TEST(ArrayQueryVariableDim, LocalparamDimensionIndexAtFixedDimIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  localparam int D = 3;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, D);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.7.1: the restriction does not touch $dimensions, which takes no dimension
// argument and so is well-defined even when an inner dimension is variable.
TEST(ArrayQueryVariableDim, DimensionsIsUnaffected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $dimensions(a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.7.1: the restriction also does not touch $unpacked_dimensions, which
// likewise takes no dimension argument.
TEST(ArrayQueryVariableDim, UnpackedDimensionsIsUnaffected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $unpacked_dimensions(a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.7.1: each element of the first dimension of `int a[3][][5]` holds a
// dynamic array of its own size, so a query of dimension 2 has no single
// answer and is an error. The subclause on the report is what tells this
// rejection from §20.7's own rules about the query functions, which the same
// call satisfies: it names a query function that exists and a dimension the
// array has.
TEST(ArrayQueryVariableDim, SizeOfDynamicInnerDimensionNames20_7_1) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int a[3][][5];\n"
             "  int n;\n"
             "  initial n = $size(a, 2);\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot query variable-sized dimension 2 of array "
                            "'a'",
                            4, "20.7.1"));
}

// §20.7.1 says that when a §20.7 query function is "called with arguments (v,
// n) where v denotes some array variable and n is greater than 1, then it
// shall be an error if the dimension indicated by n is a variable-sized
// dimension", and names no position the call may stand in. Each of the five
// cases below writes the call in one such position, and each is a position
// CheckArrayQueryOnVarDimStmt in
// src/elaborator/elaborator_validate_queries.cpp reached only once it took its
// list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Every one of them elaborated
// clean beforehand, with an inner variable-sized dimension left queried.
//
// Each case names a different query function, and the three forms §20.7 counts
// as variable-sized -- the dynamic array, the queue and the wildcard
// associative array -- are spread across them.

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and a §20.7 query
// function returns a value, so a call stands as the right-hand side of the
// operator_assignment the loop step is written as. The parser keeps that
// statement in Stmt::for_steps.
TEST(ArrayQueryVariableDim, SizeOfDynamicInnerDimensionInAForStepIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int qa[3][][5];\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; i = $size(qa, 2))\n"
      "      i = i + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'qa'",
                            5, "20.7.1"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// The parser keeps the pass arm in Stmt::assert_pass_stmt.
TEST(ArrayQueryVariableDim,
     LowOfDynamicInnerDimensionInAnAssertionPassStatementIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int pa[4][][2];\n"
      "  int n;\n"
      "  logic ready;\n"
      "  initial assert (ready) n = $low(pa, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$low' cannot query "
                            "variable-sized dimension 2 of array 'pa'",
                            5, "20.7.1"));
}

// §16.3's else arm of the same action block, kept in Stmt::assert_fail_stmt.
// The inner dimension here is a queue, the second of the three variable-sized
// forms.
TEST(ArrayQueryVariableDim,
     HighOfQueueInnerDimensionInAnAssertionFailStatementIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int qb[2][$];\n"
      "  int n;\n"
      "  logic go;\n"
      "  initial assert (go) else n = $high(qb, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$high' cannot query "
                            "variable-sized dimension 2 of array 'qb'",
                            5, "20.7.1"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The inner
// dimension here is a wildcard associative array, the third variable-sized
// form.
TEST(ArrayQueryVariableDim,
     IncrementOfWildcardAssocInnerDimensionInARandcaseItemIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int wa[2][*];\n"
      "  int n;\n"
      "  initial randcase 1: n = $increment(wa, 2); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$increment' cannot query "
                            "variable-sized dimension 2 of array 'wa'",
                            4, "20.7.1"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(ArrayQueryVariableDim,
     RightOfDynamicInnerDimensionInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int ra[3][][6];\n"
      "  int n;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { n = $right(ra, 2); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$right' cannot query "
                            "variable-sized dimension 2 of array 'ra'",
                            6, "20.7.1"));
}

}  // namespace
