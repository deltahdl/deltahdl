#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §20.7 states that an array query function call is legal within a constant
// expression when the type of its first argument is a fixed-size type, even
// though the data object named by that argument is not itself a constant. The
// elaborator must therefore treat such a call as constant even when its
// operand is not a constant operand. Each query function is exercised with a
// non-constant (undeclared, hence out-of-scope) array operand.

TEST(ArrayQueryConstExpr, SizeWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$size(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

TEST(ArrayQueryConstExpr, DimensionsWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$dimensions(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

TEST(ArrayQueryConstExpr, UnpackedDimensionsWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$unpacked_dimensions(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

TEST(ArrayQueryConstExpr, LeftWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$left(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

TEST(ArrayQueryConstExpr, RightWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$right(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

TEST(ArrayQueryConstExpr, LowWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$low(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

TEST(ArrayQueryConstExpr, HighWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$high(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

TEST(ArrayQueryConstExpr, IncrementWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$increment(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

// A query with an explicit constant dimension expression is also constant.
TEST(ArrayQueryConstExpr, SizeWithDimensionExprIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$size(arr, 2)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

// §20.7: applying an array query function directly to a dynamically sized type
// identifier (here a queue typedef) is an elaboration error, because a dynamic
// dimension has no extent outside of an object instance.
TEST(ArrayQueryOnType, QueryOnQueueTypedefIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  initial n = $size(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot be applied "
                            "directly to dynamically sized type 'qt'",
                            4, "20.7"));
}

// §20.7: the same query on a fixed-size type identifier is legal, confirming
// the rule rejects only dynamically sized type identifiers.
TEST(ArrayQueryOnType, QueryOnFixedTypedefIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef logic [3:0] ft;\n"
      "  int n;\n"
      "  initial n = $size(ft);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.7 bars an array query function applied directly to a dynamically sized
// type identifier and puts no condition on where the query is written, so every
// position a statement holds a statement in is a position the report is made
// at. CheckArrayQueryOnDynamicTypeStmt in
// src/elaborator/elaborator_validate_matches.cpp had written out eight of the
// thirteen child-statement links Stmt declares, and now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. The cases
// below cover one newly reached position each.

// Stmt::for_steps holds a for loop's step assignments, a member of its own
// beside the initializers the walk already reached.
TEST(ArrayQueryOnType, QueryOnQueueTypedefInAForStepIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; n = $size(qt)) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot be applied "
                            "directly to dynamically sized type 'qt'",
                            5, "20.7"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(ArrayQueryOnType,
     QueryOnQueueTypedefInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  logic ok;\n"
      "  initial assert (ok) n = $size(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot be applied "
                            "directly to dynamically sized type 'qt'",
                            5, "20.7"));
}

TEST(ArrayQueryOnType,
     QueryOnQueueTypedefInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  logic ok;\n"
      "  initial assert (ok) else n = $size(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot be applied "
                            "directly to dynamically sized type 'qt'",
                            5, "20.7"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items. §20.7 is a rule about the source, so it holds whether
// the weighted draw would select the item or not.
TEST(ArrayQueryOnType, QueryOnQueueTypedefInARandcaseItemIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  initial randcase 1: n = $size(qt); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot be applied "
                            "directly to dynamically sized type 'qt'",
                            4, "20.7"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(ArrayQueryOnType, QueryOnQueueTypedefInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { n = $size(qt); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot be applied "
                            "directly to dynamically sized type 'qt'",
                            6, "20.7"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(ArrayQueryOnType,
     QueryOnQueueTypedefInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { n = $size(qt); };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot be applied "
                            "directly to dynamically sized type 'qt'",
                            7, "20.7"));
}

}  // namespace
