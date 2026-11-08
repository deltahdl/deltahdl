#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_config_params.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

namespace {

TEST(ConfigLocalparamLiteral, StringLocalparamReachesTheInstanceWhole) {
  ElabFixture f;
  auto* child = ConfigElabFirstChild(
      f,
      "module adder #(parameter ID = \"id\", W = 8); endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config cfg;\n"
      "  localparam ID = \"abcdef\";\n"
      "  localparam W = 100;\n"
      "  design top;\n"
      "  instance top.a1 use #(.ID(ID), .W(W));\n"
      "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(child, nullptr);
  const Expr* id = OverrideExpr(child, "ID");
  ASSERT_NE(id, nullptr);
  EXPECT_EQ(id->kind, ExprKind::kStringLiteral);
  EXPECT_NE(id->text.find("abcdef"), std::string_view::npos) << id->text;
  EXPECT_EQ(ResolvedParam(child, "W"), 100);
}

TEST(ConfigParamOverride, TypeParameterSetByNamedAssignment) {
  ElabFixture f;
  auto* child = ConfigElabFirstChild(
      f,
      "module holder #(parameter type T = byte); T v; endmodule\n"
      "module top; holder h(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  instance top.h use #(.T(shortint));\n"
      "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(VariableWidth(child, "v"), 16u);
}

TEST(ConfigParamOverride, TypeParameterOverrideBeatsTheInstantiation) {
  ElabFixture f;
  auto* child = ConfigElabFirstChild(
      f,
      "module holder #(parameter type T = byte); T v; endmodule\n"
      "module top; holder #(.T(int)) h(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  instance top.h use #(.T(shortint));\n"
      "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(VariableWidth(child, "v"), 16u);
}

TEST(ConfigParamOverride, EmptyTypeParameterAssignmentResetsToTheDefault) {
  ElabFixture f;
  auto* child = ConfigElabFirstChild(
      f,
      "module holder #(parameter type T = byte); T v; endmodule\n"
      "module top; holder #(.T(int)) h(); endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "  instance top.h use #(.T());\n"
      "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(VariableWidth(child, "v"), 8u);
}

TEST(ConfigParamOverride, HierarchicalReferenceToTheParentsHeaderParameter) {
  ElabFixture f;
  auto* child = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8); endmodule\n"
      "module top #(parameter WIDTH = 16); adder a1(); endmodule\n"
      "config cfg1;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH));\n"
      "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(ResolvedParam(child, "W"), 16);
}

TEST(ConfigParamOverride, HierarchicalReferenceToTheParentsBodyParameter) {
  ElabFixture f;
  auto* child = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8); endmodule\n"
      "module top; parameter WIDTH = 16; adder a1(); endmodule\n"
      "config cfg1;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH));\n"
      "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(ResolvedParam(child, "W"), 16);
}

TEST(ConfigParamOverride, HierarchicalReferenceIsNotTheConfigsLocalparam) {
  ElabFixture f;
  auto* child = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8); endmodule\n"
      "module top4; parameter S = 16; adder a1(); endmodule\n"
      "config cfg2;\n"
      "  localparam S = 24;\n"
      "  design top4;\n"
      "  instance top4.a1 use #(.W(top4.S));\n"
      "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(ResolvedParam(child, "W"), 16);
}

TEST(ConfigParamOverride, HierarchicalParameterArrayIndexedByALocalparam) {
  ElabFixture f;
  auto* child =
      ConfigElabFirstChild(f,
                           "module adder #(parameter W = 8); endmodule\n"
                           "module top;\n"
                           "  parameter int PARR[3] = '{10, 20, 30};\n"
                           "  adder a1();\n"
                           "endmodule\n"
                           "config cfg;\n"
                           "  localparam I = 2;\n"
                           "  design top;\n"
                           "  instance top.a1 use #(.W(top.PARR[I]));\n"
                           "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(ResolvedParam(child, "W"), 30);
}

RtlirModule* ConfigElabTop(ElabFixture& f, const std::string& src) {
  auto* design = ConfigElab(f, src);
  if (!design || design->top_modules.size() != 1) return nullptr;
  return design->top_modules[0];
}

TEST(ConfigParamOverride, InstanceClauseOnTheTopCellSetsAHeaderParameter) {
  ElabFixture f;
  auto* top = ConfigElabTop(f,
                            "module top #(parameter WIDTH = 16); endmodule\n"
                            "config cfg1;\n"
                            "  design top;\n"
                            "  instance top use #(.WIDTH(32));\n"
                            "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(ResolvedParam(top, "WIDTH"), 32);
}

TEST(ConfigParamOverride, InstanceClauseOnTheTopCellSetsABodyParameter) {
  ElabFixture f;
  auto* top = ConfigElabTop(f,
                            "module top; parameter WIDTH = 16; endmodule\n"
                            "config cfg1;\n"
                            "  design top;\n"
                            "  instance top use #(.WIDTH(32));\n"
                            "endconfig\n");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(ResolvedParam(top, "WIDTH"), 32);
}

TEST(ConfigLocalparamLiteral, NonLiteralLocalparamRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = 1 + 2;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' localparam 'X' is not assigned a "
                            "literal value",
                            3, "33.4.3"));
}

TEST(ConfigLocalparamLiteral, IdentifierLocalparamRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = a;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' localparam 'X' is not assigned a "
                            "literal value",
                            3, "33.4.3"));
}

TEST(ConfigLocalparamLiteral, IntegerLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam X = 8;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, StringLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam S = \"name\";\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, RealLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam R = 1.5;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, UnbasedUnsizedLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam U = '1;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, TimeLiteralLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam T = 5ns;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, HierIdentInExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "config 'c' override of parameter 'W' embeds a "
                    "hierarchical identifier inside a larger expression",
                    4, "33.4.3"));
}

TEST(ConfigParamOverride, ReportStandsAtTheOffendingUseClause) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(8));\n"
      "  instance top.a2 use #(.W(top.WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "config 'c' override of parameter 'W' embeds a "
                    "hierarchical identifier inside a larger expression",
                    5, "33.4.3"));
}

TEST(ConfigParamOverride, HierIdentAloneAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.WIDTH));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, NonHierIdentInExpressionAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(WIDTH + 7));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigLocalparamLiteral, DeclaredTypeConvertsTheLiteral) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(f,
                                  "module adder #(parameter W = 3); endmodule\n"
                                  "module top; adder a1(); endmodule\n"
                                  "config c;\n"
                                  "  localparam bit [3:0] S = 24;\n"
                                  "  design top;\n"
                                  "  instance top.a1 use #(.W(S));\n"
                                  "endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 8);
}

TEST(ConfigLocalparamLiteral, TypeLocalparamRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam type T = int;\n"
      "  design top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' localparam 'T' is a type, not a "
                            "literal value",
                            3, "33.4.3"));
}

TEST(ConfigParamOverride, IndexUsingUnknownIdentifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[i]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' uses index "
                            "identifier 'i' that is neither a literal nor a "
                            "localparam of the config",
                            4, "33.4.3"));
}

TEST(ConfigParamOverride, IndexUsingLiteralAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[2]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, IndexUsingConfigLocalparamAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  localparam IDX = 0;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[IDX]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, IndexOfAPlainNameIsNotRestricted) {
  ElabFixture f;
  ElaborateSrc(
      "module adder #(parameter W = 8); endmodule\n"
      "module top;\n"
      "  parameter int PARR[4] = '{1, 2, 3, 4};\n"
      "  parameter K = 1;\n"
      "  adder a1();\n"
      "endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(PARR[K]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, PackageScopedNameInALargerExpressionAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package p; parameter X = 4; endpackage\n"
      "module adder #(parameter W = 8); endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(p::X + 1));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, HierRefThroughArrayOfInstancesRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.arr[0].WIDTH));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' uses a "
                            "hierarchical reference that traverses an array of "
                            "instances",
                            4, "33.4.3"));
}

TEST(ConfigParamOverride, HierRefThroughGenerateScopeRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module adder #(parameter W = 8); endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    parameter GW = 20;\n"
      "  end\n"
      "  adder a1();\n"
      "endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.g.GW));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' uses a "
                            "hierarchical reference that passes through a "
                            "generate scope",
                            10, "33.4.3"));
}

TEST(ConfigParamOverride, RelativeHierRefThroughGenerateScopeRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module adder #(parameter W = 8); endmodule\n"
      "module top;\n"
      "  for (genvar i = 0; i < 1; i++) begin : g\n"
      "    localparam GW = 20;\n"
      "  end\n"
      "  adder a1();\n"
      "endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(g.GW));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "passes through a generate scope", 10, "33.4.3"));
}

TEST(ConfigParamOverride, HierRefThroughModuleInstanceNotAGenerateScope) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf #(parameter LW = 5); endmodule\n"
      "module adder #(parameter W = 8); endmodule\n"
      "module top;\n"
      "  leaf g();\n"
      "  adder a1();\n"
      "endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.g.LW));\n"
      "endconfig\n",
      f, "top");
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_EQ(d.message.find("generate scope"), std::string::npos) << d.message;
  }
}

TEST(ConfigParamOverride, UserFunctionCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(my_func(8)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' calls a "
                            "user-defined function; only built-in constant "
                            "functions are permitted",
                            4, "33.4.3"));
}

TEST(ConfigParamOverride, SystemFunctionCallAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W($clog2(8)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, EmptyParamOverrideAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W());\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, EmptyParamListAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #();\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigParamOverride, RangeSelectBoundNonLiteralRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.PARAM[2:i]));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' uses index "
                            "identifier 'i' that is neither a literal nor a "
                            "localparam of the config",
                            4, "33.4.3"));
}

TEST(ConfigParamOverride, NestedUserFunctionCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(1 + my_func(2)));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' calls a "
                            "user-defined function; only built-in constant "
                            "functions are permitted",
                            4, "33.4.3"));
}

TEST(ConfigParamApply, OverrideSetsInstanceParameter) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config c; design top; instance top.a1 use #(.W(32)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 32);
}

TEST(ConfigParamApply, OverrideUsingConfigLocalparamValue) {
  ElabFixture f;
  auto* a1 =
      ConfigElabFirstChild(f,
                           "module adder #(parameter W = 8) (); endmodule\n"
                           "module top; adder a1(); endmodule\n"
                           "config c; localparam V = 24; design top;\n"
                           "  instance top.a1 use #(.W(V)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 24);
}

TEST(ConfigParamApply, OverrideUsingParentParameterValue) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; parameter P = 20; adder a1(); endmodule\n"
      "config c; design top; instance top.a1 use #(.W(P)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 20);
}

TEST(ConfigParamApply, EmptyOverrideResetsParameterToDefault) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; adder #(.W(16)) a1 (); endmodule\n"
      "config c; design top; instance top.a1 use #(.W()); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 8);
}

TEST(ConfigParamApply, EmptyListResetsAllParametersToDefault) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8, parameter D = 4) (); endmodule\n"
      "module top; adder #(.W(16), .D(2)) a1 (); endmodule\n"
      "config c; design top; instance top.a1 use #(); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 8);
  EXPECT_EQ(ResolvedParam(a1, "D"), 4);
}

TEST(ConfigParamApply, OverrideTakesPrecedenceOverDefparam) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8) (); endmodule\n"
      "module top; adder a1(); defparam a1.W = 16; endmodule\n"
      "config c; design top; instance top.a1 use #(.W(32)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 32);
}

TEST(ConfigParamApply, UseClauseNamingABodyParameterUnderAPortListIsRejected) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c #(parameter W = 1); parameter P = 2; endmodule\n"
      "module top; c u(); endmodule\n"
      "config cfg; design top;\n"
      "  instance top.u use #(.P(5));\n"
      "endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "configuration cannot override a local parameter: "
                            "'P' of module 'c'",
                            4, "6.20.4"));
  EXPECT_EQ(ResolvedParam(u, "P"), 2);
}

TEST(ConfigParamApply, UseClauseOnABodyParameterOfAModuleWithoutAPortList) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c; parameter P = 2; endmodule\n"
      "module top; c u(); endmodule\n"
      "config cfg; design top; instance top.u use #(.P(5)); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(u, "P"), 5);
}

TEST(ConfigParamApply, EmptyListLocksABodyParameterAgainstADefparam) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c; parameter P = 2; endmodule\n"
      "module top; c #(.P(7)) u(); defparam u.P = 9; endmodule\n"
      "config cfg; design top; instance top.u use #(); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(u, "P"), 2);
}

TEST(ConfigParamApply, NamedUseClauseLocksABodyParameterAgainstADefparam) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c; parameter P = 2; endmodule\n"
      "module top; c u(); defparam u.P = 9; endmodule\n"
      "config cfg; design top; instance top.u use #(.P(5)); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(u, "P"), 5);
}

TEST(ConfigParamApply, UseClauseLeavesAnUnnamedBodyParameterToADefparam) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c; parameter P = 2; parameter Q = 3; endmodule\n"
      "module top; c u(); defparam u.Q = 9; endmodule\n"
      "config cfg; design top; instance top.u use #(.P(5)); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(u, "P"), 5);
  EXPECT_EQ(ResolvedParam(u, "Q"), 9);
}

TEST(ConfigParamApply, UseClauseNamingNoParameterOfTheModuleIsRejected) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(f,
                                 "module c; parameter P = 2; endmodule\n"
                                 "module top; c u(); endmodule\n"
                                 "config cfg; design top;\n"
                                 "  instance top.u use #(.X(5), .P(7));\n"
                                 "endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'c' has no parameter 'X'", 4, "23.10.2.2"));
  EXPECT_EQ(ResolvedParam(u, "P"), 7);
}

TEST(ConfigParamApply, UseClauseNamingNoParameterOfAPortListIsRejected) {
  ElabFixture f;
  auto* u = ConfigElabFirstChild(
      f,
      "module c #(parameter W = 1); endmodule\n"
      "module top; c u(); endmodule\n"
      "config cfg; design top; instance top.u use #(.X(5)); endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'c' has no parameter 'X'", 3, "23.10.2.2"));
  EXPECT_EQ(ResolvedParam(u, "W"), 1);
}

}  // namespace
