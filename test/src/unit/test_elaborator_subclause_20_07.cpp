#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_param_value.h"
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

std::string DynamicTypeMessage(const char* fn, const char* type) {
  std::string m = "array query function '";
  m += fn;
  m += "' cannot be applied directly to dynamically sized type '";
  m += type;
  m += "'";
  return m;
}

std::string AssociativeMessage(const char* fn, const char* array) {
  std::string m = "array query function '";
  m += fn;
  m += "' cannot be used on the associative dimension of '";
  m += array;
  m += "'";
  return m;
}

TEST(ArrayQueryReports,
     DISABLED_ASecondArgumentToAOneOperandFunctionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[2][3];\n"
      "  int x, y, z;\n"
      "  initial begin\n"
      "    x = $dimensions(a, 2);\n"
      "    y = $unpacked_dimensions(a, 2);\n"
      "    z = $dimensions(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array query function '$dimensions' takes exactly one argument", 5,
      "20.7"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array query function '$unpacked_dimensions' takes exactly one argument",
      6, "20.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayQueryReports,
     DISABLED_APerDimensionFunctionWithNoneOrThreeArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[2][3];\n"
      "  int r[7];\n"
      "  initial begin\n"
      "    r[0] = $size();\n"
      "    r[1] = $size(a, 1, 2);\n"
      "    r[2] = $left(a, 1, 2);\n"
      "    r[3] = $right(a, 1, 2);\n"
      "    r[4] = $low(a, 1, 2);\n"
      "    r[5] = $high(a, 1, 2);\n"
      "    r[6] = $increment(a, 1, 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array query function '$size' takes one or two arguments", 5, "20.7"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array query function '$size' takes one or two arguments", 6, "20.7"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array query function '$left' takes one or two arguments", 7, "20.7"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array query function '$right' takes one or two arguments", 8, "20.7"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array query function '$low' takes one or two arguments", 9, "20.7"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array query function '$high' takes one or two arguments", 10, "20.7"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array query function '$increment' takes one or two arguments", 11,
      "20.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 7u);
}

TEST(ArrayQueryReports, OneOrTwoArgumentsAreAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int a[2][3];\n"
             "  int x, y, z;\n"
             "  initial begin\n"
             "    x = $size(a);\n"
             "    y = $size(a, 2);\n"
             "    z = $dimensions(int);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ArrayQueryReports, DISABLED_ADynamicArrayOrAssociativeTypedefIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef byte dt[];\n"
      "  typedef byte ai[int];\n"
      "  typedef byte as[string];\n"
      "  typedef byte aw[*];\n"
      "  int r[4];\n"
      "  initial begin\n"
      "    r[0] = $size(dt);\n"
      "    r[1] = $size(ai);\n"
      "    r[2] = $size(as);\n"
      "    r[3] = $size(aw);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "dt"), 8, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "ai"), 9, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "as"), 10, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "aw"), 11, "20.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(ArrayQueryReports, EveryFunctionOnAQueueTypedefIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef int qt[$];\n"
      "  int r[7];\n"
      "  initial begin\n"
      "    r[0] = $left(qt);\n"
      "    r[1] = $right(qt);\n"
      "    r[2] = $low(qt);\n"
      "    r[3] = $high(qt);\n"
      "    r[4] = $increment(qt);\n"
      "    r[5] = $dimensions(qt);\n"
      "    r[6] = $unpacked_dimensions(qt);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$left", "qt"), 5, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$right", "qt"), 6, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$low", "qt"), 7, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$high", "qt"), 8, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$increment", "qt"), 9, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$dimensions", "qt"), 10,
                            "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$unpacked_dimensions", "qt"),
                            11, "20.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 7u);
}

TEST(ArrayQueryReports,
     AQueueTypedefQueriedInAFunctionOrInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef int qt[$];\n"
      "  function int f();\n"
      "    return $size(qt);\n"
      "  endfunction\n"
      "  int v = $size(qt);\n"
      "  localparam int L = $size(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "qt"), 4, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "qt"), 6, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "qt"), 7, "20.7"));
}

TEST(ArrayQueryReports,
     DISABLED_ADynamicTypedefInAPackageFunctionOrClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  typedef int qt[$];\n"
      "  function int f();\n"
      "    return $size(qt);\n"
      "  endfunction\n"
      "endpackage\n"
      "class C;\n"
      "  typedef int dt[];\n"
      "  function int g();\n"
      "    return $size(dt);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "qt"), 4, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "dt"), 10, "20.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayQueryReports,
     DISABLED_ADynamicTypedefOfTheCompilationUnitOrAnImportIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int ut[$];\n"
      "package pk;\n"
      "  typedef int pt[];\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::*;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = $size(ut);\n"
      "    b = $size(pt);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "ut"), 9, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            DynamicTypeMessage("$size", "pt"), 10, "20.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayQueryReports, AStringIndexedArrayInAFunctionOrInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  int a2[3][string];\n"
      "  function int f();\n"
      "    return $size(aa);\n"
      "  endfunction\n"
      "  int n = $size(aa);\n"
      "  int k;\n"
      "  initial k = $size(a2, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            AssociativeMessage("$size", "aa"), 5, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            AssociativeMessage("$size", "aa"), 7, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            AssociativeMessage("$size", "a2"), 9, "20.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(ArrayQueryReports,
     DISABLED_AStringIndexedPropertyInAClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int aa[string];\n"
      "  function int f();\n"
      "    return $size(aa);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            AssociativeMessage("$size", "aa"), 4, "20.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ArrayQueryReports, DISABLED_AClassIndexedArrayIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module t;\n"
      "  C aa[C];\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = $size(aa);\n"
      "    b = $low(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            AssociativeMessage("$size", "aa"), 6, "20.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            AssociativeMessage("$low", "aa"), 7, "20.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayQueryConstant, AQueryOverADynamicArrayIsNoConstantExpression) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  localparam int A = $dimensions(d);\n"
      "  localparam int B = $size(d, 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'A' initializer is not a constant expression", 3, "6.20.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'B' initializer is not a constant expression", 4, "6.20.4"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayQueryConstant,
     DISABLED_ANonConstantDimensionMakesTheQueryNonConstant) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[2][3];\n"
      "  int k = 1;\n"
      "  localparam int L = $size(a, k);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'L' initializer is not a constant expression", 4, "6.20.4"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ArrayQueryConstant,
     DISABLED_AQueryOverAnUndeclaredNameIsNoConstantExpression) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  localparam int L = $size(nothing);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'L' initializer is not a constant expression", 2, "6.20.4"));
}

TEST(ArrayQueryConstant, DISABLED_ATypeOperatorAndTheResultWidthFold) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int fa[4];\n"
      "  localparam int K = $size(fa);\n"
      "  localparam int L = $dimensions(type(fa));\n"
      "  localparam int S = $size(type(fa));\n"
      "  localparam int W = $bits($size(fa));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "K"), 4);
  EXPECT_EQ(ParamValue(design, "L"), 2);
  EXPECT_EQ(ParamValue(design, "S"), 4);
  EXPECT_EQ(ParamValue(design, "W"), 32);
}

}  // namespace
