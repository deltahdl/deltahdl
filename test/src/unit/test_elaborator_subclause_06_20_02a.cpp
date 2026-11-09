#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(ValueParameters, RealParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter real r = 5.7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters, ModuleWithTypedParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters, MultipleParamsResolveCorrectValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter e = 25, f = 9;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "e");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 25);
  EXPECT_EQ(design->top_modules[0]->params[1].name, "f");
  EXPECT_EQ(design->top_modules[0]->params[1].resolved_value, 9);
}

TEST(ValueParameters, ParameterRefResolvesValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = 5;\n"
      "  parameter int B = A;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_TRUE(b.is_resolved);
  EXPECT_EQ(b.resolved_value, 5);
}

TEST(ValueParameters, DependentParamResolvesValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  parameter int MASK = (1 << WIDTH) - 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& mask = design->top_modules[0]->params[1];
  EXPECT_EQ(mask.name, "MASK");
  EXPECT_TRUE(mask.is_resolved);
  EXPECT_EQ(mask.resolved_value, 255);
}

TEST(ValueParameters, UntypedUnrangedHasNoDeclaredTypeOrRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_FALSE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.resolved_value, 42);
}

TEST(ValueParameters, RangedUntypedIsUnsignedWithDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [7:0] P = 200;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_range);
  EXPECT_FALSE(p.has_decl_type);
  EXPECT_FALSE(p.decl_is_signed);
  EXPECT_EQ(p.decl_width, 8u);
}

TEST(ValueParameters, TypedUnrangedTakesDeclaredType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 32u);
}

TEST(ValueParameters, SignedRangedIsSignedWithDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter signed [3:0] s = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_TRUE(p.has_decl_range);
  EXPECT_TRUE(p.decl_is_signed);
  EXPECT_EQ(p.decl_width, 4u);
}

TEST(ValueParameters, OverrideDoesNotAffectUnsignedRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter [3:0] P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(255) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].name, "P");
  EXPECT_EQ(child->params[0].resolved_value, 15);
}

TEST(ValueParameters, OverrideDoesNotAffectSignedRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter signed [3:0] P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(8)) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].resolved_value, -8);
}

TEST(ValueParameters, OverrideOnSignedImplicitFollowsValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter signed P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(5)) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].resolved_value, 5);
}

TEST(ValueParameters, PartSelectOfIntegralParameterAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam [7:0] P = 8'hAB;\n"
      "  localparam X = P[3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& x = design->top_modules[0]->params[1];
  EXPECT_EQ(x.name, "X");
  EXPECT_TRUE(x.is_resolved);
  EXPECT_EQ(x.resolved_value, 0xB);
}

TEST(ValueParameters, BitSelectOfIntegralParameterAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam [7:0] P = 8'hAB;\n"
      "  localparam B = P[7];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_TRUE(b.is_resolved);
  EXPECT_EQ(b.resolved_value, 1);
}

TEST(ValueParameters, LocalParamSetFromLocalParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam A = 5;\n"
      "  localparam B = A;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_TRUE(b.is_resolved);
  EXPECT_EQ(b.resolved_value, 5);
}

TEST(ValueParameters, ByteTypedParameterTakesByteWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter byte W = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 8u);
}

TEST(ValueParameters, SignedOverrideRoundTripsNegative) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter signed [3:0] P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(-2)) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].resolved_value, -2);
}

TEST(ValueParameters, IntegerParameterFromRealConstantRounds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = 5.7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "W");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 6);
}

TEST(ValueParameters, RangedUntypedParameterAppliesRealToIntConversion) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [7:0] P = 5.7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.has_decl_range);
  EXPECT_FALSE(p.has_decl_type);
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 6);
}

TEST(ValueParameters, IntegerParameterFromNegativeRealRoundsAwayFromZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter integer N = -2.5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "N");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, -3);
}

TEST(ValueParameters, ShortintTypedParameterTakesShortintWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter shortint W = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 16u);
}

TEST(ValueParameters, LongintTypedParameterTakesLongintWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter longint W = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 64u);
}

TEST(ValueParameters, BitTypedParameterTakesSingleBitWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter bit B = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 1u);
}

TEST(ValueParameters, NegativeOverrideIntoUnsignedRangeBecomesUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter [3:0] P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(-1) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].resolved_value, 15);
}

TEST(ValueParameters, IntegerParameterFromPositiveHalfRoundsAwayFromZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = 2.5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "W");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 3);
}

TEST(ValueParameters, PartSelectOfIntegerTypedParameterAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int P = 8'hAB;\n"
      "  localparam B = P[3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_TRUE(b.is_resolved);
  EXPECT_EQ(b.resolved_value, 0xB);
}

TEST(ValueParameters, BitSelectOfRealParameterRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter real R = 1.5;\n"
      "  logic x;\n"
      "  assign x = R[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real parameter is illegal", 4,
                            "11.5.1"));
}

TEST(ValueParameters, HierarchicalReferenceInConditionalDefaultNamesItsLine) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(\n"
      "    parameter int P = sel ? top.a : 0\n"
      "  );\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "parameter 'P' value contains a hierarchical reference", 2, "6.20.2"));
}

TEST(ValueParameters, NonConstantClassParamDefaultIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] v;\n"
      "endmodule\n"
      "class C #(int P = v);\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class parameter 'P' value is not a constant expression", 4, "6.20.2"));
}

TEST(ValueParameters, NonConstantClassBodyParamDefaultIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] v;\n"
      "endmodule\n"
      "class C;\n"
      "  localparam int P = v;\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class parameter 'P' value is not a constant expression", 5, "6.20.2"));
}

TEST(ValueParameters, ClassHandleClassParamTakesNullButNoVariable) {
  const char* const kAccepted[] = {
      "class K;\nendclass\nclass C;\n  parameter K H = null;\n"
      "  parameter K A [2] = '{null, null};\nendclass\nmodule m;\nendmodule\n",
      "class K;\nendclass\nclass C #(\n    parameter K H = null,\n"
      "    parameter K A [2] = '{null, null});\nendclass\nmodule m;\n"
      "endmodule\n",
  };
  for (const char* src : kAccepted) {
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.has_errors);
  }
  struct Rejected {
    const char* src;
    uint32_t line;
  };
  const Rejected kRejected[] = {
      {"class K;\nendclass\nclass C;\n  K v;\n  parameter K D = v;\n"
       "endclass\nmodule m;\nendmodule\n",
       5},
      {"class K;\nendclass\nclass C;\n  K v;\n"
       "  parameter K D [2] = '{null, v};\nendclass\nmodule m;\nendmodule\n",
       5},
      {"class K;\nendclass\nK v;\nclass C #(parameter K D = v);\nendclass\n"
       "module m;\nendmodule\n",
       4},
      {"class K;\nendclass\nK v;\n"
       "class C #(parameter K D [2] = '{null, v});\nendclass\nmodule m;\n"
       "endmodule\n",
       4},
  };
  for (const Rejected& c : kRejected) {
    SCOPED_TRACE(c.src);
    ElabFixture f;
    ElaborateSrc(c.src, f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "class parameter 'D' value is not a constant expression",
                      c.line, "6.20.2"));
  }
}

TEST(ValueParameters, ClassParamDefaultDependsOnEarlierClassParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "endmodule\n"
      "class C #(int A = 4, int B = A * 2);\n"
      "endclass\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters, ClassParamDefaultComputedFromTypeParamIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "endmodule\n"
      "class C #(type T = int, int S = $bits(T));\n"
      "endclass\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters,
     HierarchicalParameterReferenceInParameterValueIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  parameter int K = parent.P;\n"
      "endmodule\n"
      "module parent;\n"
      "  parameter int P = 8;\n"
      "  child c1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "parameter 'K' value contains a hierarchical reference", 2, "6.20.2"));
}

TEST(ValueParameters,
     HierarchicalParameterReferenceInLocalparamValueIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  localparam int K = parent.P;\n"
      "endmodule\n"
      "module parent;\n"
      "  parameter int P = 8;\n"
      "  child c1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "parameter 'K' value contains a hierarchical reference", 2, "6.20.2"));
}

TEST(ValueParameters, HierarchicalVariableReferenceInParameterValueIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  parameter int K = parent.v;\n"
      "endmodule\n"
      "module parent;\n"
      "  integer v;\n"
      "  child c1();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "parameter 'K' value contains a hierarchical reference", 2, "6.20.2"));
}

TEST(ValueParameters, PackageParameterReferenceInParameterValueIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int N = 4;\n"
      "endpackage\n"
      "module m;\n"
      "  parameter int K = p::N;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters, PackageParameterReferenceInLocalparamValueIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int N = 4;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int K = p::N;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters, PackageParameterReferenceResolvesItsValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int N = 4;\n"
      "endpackage\n"
      "module m;\n"
      "  parameter int K = p::N;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* k = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "K") k = &param;
  }
  ASSERT_NE(k, nullptr);
  EXPECT_TRUE(k->is_resolved);
  EXPECT_EQ(k->resolved_value, 4);
}

TEST(ValueParameters, MethodCallOnAStringParameterIsAcceptedInAParameterValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter string NAME = \"abc\";\n"
      "  parameter int W = NAME.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters, MethodCallOnAStringParameterResolvesItsValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter string NAME = \"abc\";\n"
      "  parameter int W = NAME.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* w = nullptr;
  for (const auto& param : design->top_modules[0]->params) {
    if (param.name == "W") w = &param;
  }
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_resolved);
  EXPECT_EQ(w->resolved_value, 3);
}

TEST(ValueParameters, MethodCallOnANonStringParameterReportsOnly6_20_4) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam int S = 3;\n"
      "  localparam int N = S.len();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.subclause, "6.20.2") << d.message;
  }
}

TEST(ValueParameters, NonConstantModuleScopedClassParamDefaultIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n;\n"
      "  class C #(parameter int W = n);\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class parameter 'W' value is not a constant expression", 3, "6.20.2"));
}

TEST(ValueParameters, ModuleScopedClassParamDefaultFoldsAgainstAModuleParam) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  localparam int W = 4;\n"
      "  class C #(parameter int P = W);\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters, InstanceOverrideRecordsItsExpressionAndADefaultDoesNot) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter logic [95:0] P = 96'h0, parameter int N = 1);\n"
      "endmodule\n"
      "module t;\n"
      "  c #(.P(96'h0123_4567_89AB_CDEF_0011_2233)) u();\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u, nullptr);
  ASSERT_EQ(u->params.size(), 2u);
  EXPECT_EQ(u->params[0].name, "P");
  EXPECT_TRUE(u->params[0].from_override);
  ASSERT_NE(u->params[0].override_expr, nullptr);
  EXPECT_EQ(u->params[0].override_expr->kind, ExprKind::kIntegerLiteral);
  EXPECT_NE(u->params[0].override_expr, u->params[0].default_value);
  EXPECT_EQ(u->params[1].name, "N");
  EXPECT_FALSE(u->params[1].from_override);
  EXPECT_EQ(u->params[1].override_expr, nullptr);
}

TEST(ValueParameters, WideLiteralLocalparamFoldsItsLowSixtyFourBits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam int L = P[7:0];\n"
      "  localparam int W = $bits(96'h0123_4567_89AB_CDEF_0011_2233);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* l = FindParam(design, "m", "L");
  ASSERT_NE(l, nullptr);
  EXPECT_TRUE(l->is_resolved);
  EXPECT_EQ(l->resolved_value, 0x33);
  const auto* w = FindParam(design, "m", "W");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_resolved);
  EXPECT_EQ(w->resolved_value, 96);
}

TEST(ValueParameters, SelectAtOrAboveBitSixtyFourReadsTheWideValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int M = P[71:64];\n"
      "  localparam int L8 = P[7:0];\n"
      "  localparam logic [95:0] Q = P >> 64;\n"
      "  localparam int QL = Q[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto value = [&](const char* name) {
    const auto* p = FindParam(design, "m", name);
    return p != nullptr && p->is_resolved ? p->resolved_value : -1;
  };
  EXPECT_EQ(value("H"), 0x01234567);
  EXPECT_EQ(value("M"), 0x67);
  EXPECT_EQ(value("L8"), 0x33);
  EXPECT_EQ(value("Q"), 0x01234567);
  EXPECT_EQ(value("QL"), 0x01234567);
}

}  // namespace
