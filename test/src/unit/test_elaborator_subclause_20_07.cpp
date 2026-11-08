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

TEST(ArrayQueryConstExpr, SizeWithDimensionExprIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$size(arr, 2)", f);
  EXPECT_TRUE(IsConstantExpr(e, {}));
}

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

TEST(ArrayQueryConstExpr, AQueryWhoseDimensionsAreUnknownDoesNotFold) {
  EvalFixture f;
  for (const char* text : {"$size(logic [k:0])", "$size(v[3:0])", "$size(v[2])",
                           "$size(real)", "$size(int, 2)", "$size(int, 0)",
                           "$size(int, k)", "$size()", "$left(Undeclared)"}) {
    EXPECT_FALSE(ConstEvalInt(ParseExprFrom(text, f)).has_value()) << text;
  }
}

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
  for (const char* text :
       {"$size(Arr2)", "$size(Bad)", "$size(R)", "$size(NotATypedef)"}) {
    EXPECT_FALSE(ConstEvalInt(ParseExprFrom(text, f)).has_value()) << text;
  }
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$size(type(logic [3:0]))", f)), 4);
}

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
  for (const char* text : {"$size(DA)", "$size(uv)", "$size(none)"}) {
    EXPECT_FALSE(ConstEvalInt(ParseExprFrom(text, f)).has_value()) << text;
  }
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$high(FA)", f)), 2);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$high(dv)", f)), 7);
}

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
