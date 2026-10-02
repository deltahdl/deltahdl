#include <gtest/gtest.h>

#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

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

// §20.7: use on an associative array dimension is restricted to index types
// with integral values, so a query of the string-indexed dimension of `aa`,
// with or without the dimension number, is an error.
TEST(ArrayQueryElab, AQueryOfAStringIndexedDimensionIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = $low(aa);\n"
      "    n = $size(aa, 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$low' cannot be used on "
                            "the associative dimension of 'aa', whose index "
                            "type 'string' has no integral values",
                            5, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot be used on "
                            "the associative dimension of 'aa', whose index "
                            "type 'string' has no integral values",
                            6, "20.7"));
}

// §20.7: an integral index type, and $dimensions, which counts the dimensions
// rather than querying one, stay legal on an associative array; so does a
// query of a fixed dimension of an array whose second dimension is
// string-indexed, a query whose dimension number does not fold, and a query
// of a variable that is no array.
TEST(ArrayQueryElab, IntegralIndexesAndOtherDimensionsAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int ai[int];\n"
      "  int aa[string];\n"
      "  int fs[4][string];\n"
      "  int n, k;\n"
      "  initial begin\n"
      "    n = $low(ai);\n"
      "    n = $dimensions(aa);\n"
      "    n = $size(fs, 1);\n"
      "    n = $size(aa, k);\n"
      "    n = $size(aa, 5);\n"
      "    n = $size(k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §20.7: a query folds only where its argument's dimensions are known here:
// a range that does not fold, a part- or bit-select of a variable, a type
// with no dimensions, a dimension number past the last or not constant, and a
// call with no argument are left to the run.
TEST(ArrayQueryConstExpr, AQueryWhoseDimensionsAreUnknownDoesNotFold) {
  EvalFixture f;
  for (const char* kText :
       {"$size(logic [k:0])", "$size(v[3:0])", "$size(v[2])", "$size(real)",
        "$size(int, 2)", "$size(int, 0)", "$size(int, k)", "$size()",
        "$left(Undeclared)"}) {
    EXPECT_FALSE(ConstEvalInt(ParseExprFrom(kText, f)).has_value()) << kText;
  }
}

// §20.7 with §6.18: a typedef answers for the type it names, so one naming an
// unpacked aggregate, whose dimensions the table does not carry, one whose
// packed range does not fold, one naming a real type and a name the table
// does not hold are not folded; a `type(...)` argument answers for the type it
// holds, with or without a table.
TEST(ArrayQueryConstExpr, ATypedefOrTypeOperatorFoldsForTheTypeItHolds) {
  EvalFixture f;
  DataType alias;
  alias.kind = DataTypeKind::kNamed;
  alias.type_name = "Arr";
  DataType unfolded;
  unfolded.kind = DataTypeKind::kLogic;
  unfolded.packed_dim_left = ParseExprFrom("k", f);
  unfolded.packed_dim_right = ParseExprFrom("0", f);
  DataType real_type;
  real_type.kind = DataTypeKind::kReal;
  const std::unordered_map<std::string_view, DataType> kTypedefs = {
      {"Arr2", alias}, {"Bad", unfolded}, {"R", real_type}};
  const std::unordered_set<std::string_view> kAggregates = {"Arr"};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$size(type(int))", f)), 32);
  TypedefRegistryGuard guard(&kTypedefs, &kAggregates);
  for (const char* kText :
       {"$size(Arr2)", "$size(Bad)", "$size(R)", "$size(NotATypedef)"}) {
    EXPECT_FALSE(ConstEvalInt(ParseExprFrom(kText, f)).has_value()) << kText;
  }
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$size(type(logic [3:0]))", f)), 4);
}

// §20.7: a parameter or a variable answers for its declared dimensions only
// where every one of them is fixed, so a dynamic dimension, `[]`, and a
// variable whose dimension did not fold are not folded; a fixed parameter
// array, [3] being [0:2], and a variable declared [7:4] are, $high of the
// descending [7:4] being 7.
TEST(ArrayQueryConstExpr, OnlyFixedDimensionsOfAParameterOrVariableFold) {
  EvalFixture f;
  std::vector<Expr*> dynamic_dims = {nullptr};
  std::vector<Expr*> fixed_dims = {ParseExprFrom("3", f)};
  RtlirModule mod;
  RtlirParamDecl dynamic_param;
  dynamic_param.name = "DA";
  dynamic_param.unpacked_dims = &dynamic_dims;
  RtlirParamDecl fixed_param;
  fixed_param.name = "FA";
  fixed_param.unpacked_dims = &fixed_dims;
  mod.params = {dynamic_param, fixed_param};
  RtlirVariable unfolded;
  unfolded.name = "uv";
  unfolded.num_unpacked_dims = 1;
  mod.variables.push_back(unfolded);
  RtlirVariable descending;
  descending.name = "dv";
  descending.num_unpacked_dims = 1;
  descending.unpacked_dims = {RtlirUnpackedDim{7, 4}};
  mod.variables.push_back(descending);
  ParamRangeRegistryGuard guard(&mod);
  for (const char* kText : {"$size(DA)", "$size(uv)", "$size(none)"}) {
    EXPECT_FALSE(ConstEvalInt(ParseExprFrom(kText, f)).has_value()) << kText;
  }
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$high(FA)", f)), 2);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$high(dv)", f)), 7);
}

// §20.7: an array query is a constant expression only on an argument whose
// dimensions are fixed, so one on a parameter declared with a dynamic
// dimension, or on a queue, cannot initialize a localparam (§6.20.4); one on
// a parameter whose dimension a parameter sizes can.
TEST(ArrayQueryElab, AQueryOnADynamicDimensionIsNoConstantExpression) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  parameter int DA[] = '{1, 2};\n"
      "  int q[$];\n"
      "  localparam int S = $size(DA);\n"
      "  localparam int T = $size(q);\n"
      "  parameter int N = 2;\n"
      "  parameter int C[N] = '{1, 2};\n"
      "  localparam int U = $size(C);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "localparam 'U' initializer is not a constant "
                             "expression",
                             8, "6.20.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "localparam 'S' initializer is not a constant "
                            "expression",
                            4, "6.20.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "localparam 'T' initializer is not a constant "
                            "expression",
                            5, "6.20.4"));
}

}  // namespace
