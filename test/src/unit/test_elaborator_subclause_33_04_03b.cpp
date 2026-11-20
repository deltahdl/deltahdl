#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_config_params.h"
#include "helpers_reported_error.h"

namespace {

TEST(ConfigParamOverride, HierRefThroughUnnamedGenerateBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module adder #(parameter W = 8); endmodule\n"
      "module top;\n"
      "  if (1) begin\n"
      "    localparam X = 5;\n"
      "  end\n"
      "  adder a1();\n"
      "endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.genblk1.X));\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' override of parameter 'W' uses a "
                            "hierarchical reference that passes through a "
                            "generate scope",
                            10, "33.4.3"));
}

const RtlirParamDecl* ParamNamed(const RtlirModule* m, std::string_view name) {
  for (const auto& p : m->params) {
    if (p.name == name) return &p;
  }
  return nullptr;
}

TEST(ConfigParamApply, RealOverrideReachesTheInstance) {
  ElabFixture f;
  auto* u =
      ConfigElabFirstChild(f,
                           "module c #(parameter real R = 1.0); endmodule\n"
                           "module top; c u(); endmodule\n"
                           "config cfg;\n"
                           "  design top;\n"
                           "  instance top.u use #(.R(2.5));\n"
                           "endconfig\n");
  ASSERT_NE(u, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirParamDecl* r = ParamNamed(u, "R");
  ASSERT_NE(r, nullptr);
  EXPECT_DOUBLE_EQ(r->resolved_real, 2.5);
}

TEST(ConfigParamApply, OverrideNamingNoConstantReported) {
  ElabFixture f;
  ConfigElab(f,
             "module adder #(parameter W = 8); endmodule\n"
             "module top; adder a1(); endmodule\n"
             "config cfg;\n"
             "  design top;\n"
             "  instance top.a1 use #(.W(NOPE));\n"
             "endconfig\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "configuration override of parameter 'W' of "
                            "'adder' has no constant value",
                            5, "33.4.3"));
}

TEST(ConfigParamApply, OverrideReadsAParameterAboveTheParent) {
  ElabFixture f;
  auto* design =
      ConfigElab(f,
                 "module leaf #(parameter W = 1); endmodule\n"
                 "module mid; leaf b(); endmodule\n"
                 "module top; parameter WIDTH = 7; mid a1(); endmodule\n"
                 "config cfg;\n"
                 "  design top;\n"
                 "  instance top.a1.b use #(.W(top.WIDTH));\n"
                 "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* b =
      design->top_modules[0]->children[0].resolved->children[0].resolved;
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(ResolvedParam(b, "W"), 7);
}

TEST(ConfigParamApply, TopOverrideReadsACompilationUnitParameter) {
  ElabFixture f;
  auto* design = ConfigElab(f,
                            "parameter CU_P = 5;\n"
                            "module top; parameter WIDTH = 1; endmodule\n"
                            "config cfg;\n"
                            "  design top;\n"
                            "  instance top use #(.WIDTH(CU_P));\n"
                            "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design->top_modules[0], "WIDTH"), 5);
}

TEST(ConfigParamApply, DefparamRefoldKeepsTheConfigLocalparam) {
  ElabFixture f;
  auto* design =
      ConfigElab(f,
                 "module adder #(parameter W = 8); endmodule\n"
                 "module top4; parameter S = 16, Q = 1; adder a1(); endmodule\n"
                 "module test; top4 t(); defparam t.Q = 2; endmodule\n"
                 "config cfg;\n"
                 "  localparam S = 24;\n"
                 "  design test;\n"
                 "  instance test.t.a1 use #(.W(S + 0));\n"
                 "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* a1 =
      design->top_modules[0]->children[0].resolved->children[0].resolved;
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(ResolvedParam(a1, "W"), 24);
}

const RtlirModule* ChildAt(const RtlirModule* m, size_t index) {
  if (m == nullptr || m->children.size() <= index) return nullptr;
  return m->children[index].resolved;
}

void ExpectCellUseOverrideRejected(const std::string& modules,
                                   const std::string& value,
                                   std::string_view message) {
  ElabFixture f;
  ConfigElab(f, modules +
                    "config c;\n"
                    "  design top;\n"
                    "  cell adder use #(.W(" +
                    value +
                    "));\n"
                    "endconfig\n");
  const auto kLine =
      static_cast<uint32_t>(std::count(modules.begin(), modules.end(), '\n')) +
      3;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, kLine, "33.4.3"));
}

constexpr const char* kAdderAndTop =
    "module adder #(parameter W = 8); endmodule\n"
    "module top;\n"
    "  parameter WIDTH = 4;\n"
    "  function automatic int my_func(int x); return x; endfunction\n"
    "  if (1) begin\n"
    "    localparam X = 5;\n"
    "  end\n"
    "  if (1) begin : g\n"
    "    parameter GW = 20;\n"
    "  end\n"
    "  adder arr[1:0]();\n"
    "  adder a1();\n"
    "endmodule\n";

TEST(ConfigParamOverride, CellUseUserFunctionCallRejected) {
  ExpectCellUseOverrideRejected(kAdderAndTop, "my_func(8)",
                                "calls a user-defined function");
}

TEST(ConfigParamOverride, CellUseHierIdentInExpressionRejected) {
  ExpectCellUseOverrideRejected(
      kAdderAndTop, "top.WIDTH + 7",
      "embeds a hierarchical identifier inside a larger expression");
}

TEST(ConfigParamOverride, CellUseHierRefThroughGenerateScopeRejected) {
  ExpectCellUseOverrideRejected(kAdderAndTop, "top.g.GW",
                                "passes through a generate scope");
}

TEST(ConfigParamOverride,
     DISABLED_CellUseRelativeHierRefThroughGenerateScopeRejected) {
  ExpectCellUseOverrideRejected(kAdderAndTop, "g.GW",
                                "passes through a generate scope");
}

TEST(ConfigParamOverride, CellUseHierRefThroughUnnamedGenerateBlockRejected) {
  ExpectCellUseOverrideRejected(kAdderAndTop, "top.genblk1.X",
                                "passes through a generate scope");
}

TEST(ConfigParamOverride, CellUseHierRefThroughArrayOfInstancesRejected) {
  ExpectCellUseOverrideRejected(kAdderAndTop, "top.arr[0].W",
                                "traverses an array of instances");
}

TEST(ConfigParamOverride, HierRefThroughAGenerateBlockOfASubInstanceRejected) {
  ElabFixture f;
  ConfigElab(f,
             "module adder #(parameter W = 8); endmodule\n"
             "module sub;\n"
             "  if (1) begin : g\n"
             "    localparam X = 5;\n"
             "  end\n"
             "endmodule\n"
             "module top; sub u(); adder a1(); endmodule\n"
             "config c;\n"
             "  design top;\n"
             "  instance top.a1 use #(.W(top.u.g.X));\n"
             "endconfig\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "passes through a generate scope", 10, "33.4.3"));
}

TEST(ConfigParamApply, DefparamBelowTheConfiguredInstanceStillApplies) {
  ElabFixture f;
  auto* design =
      ConfigElab(f,
                 "module adder #(parameter ID = 0, W = 8, D = 512); endmodule\n"
                 "module top8;\n"
                 "  parameter WIDTH = 32;\n"
                 "  adder #(.ID(1)) a1();\n"
                 "  adder #(.ID(2), .W(WIDTH)) a2();\n"
                 "endmodule\n"
                 "module test;\n"
                 "  top8 t();\n"
                 "  defparam t.WIDTH = 64;\n"
                 "  defparam t.a1.W = 16;\n"
                 "endmodule\n"
                 "config cfg6;\n"
                 "  design test;\n"
                 "  instance test.t use #(.WIDTH(48));\n"
                 "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* t = ChildAt(design->top_modules[0], 0);
  const RtlirModule* a1 = ChildAt(t, 0);
  const RtlirModule* a2 = ChildAt(t, 1);
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(ResolvedParam(t, "WIDTH"), 48);
  EXPECT_EQ(ResolvedParam(a1, "W"), 16);
  EXPECT_EQ(ResolvedParam(a2, "W"), 48);
}

TEST(ConfigParamApply, OverrideKeepsTheInstancesOtherAssignments) {
  ElabFixture f;
  auto* design =
      ConfigElab(f,
                 "module adder #(parameter ID = 0, W = 8, D = 512); endmodule\n"
                 "module top4;\n"
                 "  parameter S = 16;\n"
                 "  adder #(.ID(1)) a1();\n"
                 "  adder #(.ID(2)) a2();\n"
                 "  adder #(.ID(3)) a3();\n"
                 "endmodule\n"
                 "config cfg2;\n"
                 "  localparam S = 24;\n"
                 "  design top4;\n"
                 "  instance top4.a1 use #(.W(top4.S));\n"
                 "  instance top4.a2 use #(.W(S));\n"
                 "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* top = design->top_modules[0];
  const RtlirModule* a1 = ChildAt(top, 0);
  const RtlirModule* a2 = ChildAt(top, 1);
  const RtlirModule* a3 = ChildAt(top, 2);
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  ASSERT_NE(a3, nullptr);
  EXPECT_EQ(ResolvedParam(a1, "ID"), 1);
  EXPECT_EQ(ResolvedParam(a1, "W"), 16);
  EXPECT_EQ(ResolvedParam(a1, "D"), 512);
  EXPECT_EQ(ResolvedParam(a2, "ID"), 2);
  EXPECT_EQ(ResolvedParam(a2, "W"), 24);
  EXPECT_EQ(ResolvedParam(a3, "ID"), 3);
  EXPECT_EQ(ResolvedParam(a3, "W"), 8);
}

TEST(ConfigParamApply, ABareNameResolvesToTheParentNotTheInstance) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "module adder #(parameter W = 8, P = 3); endmodule\n"
      "module top; parameter P = 20; adder a1(); endmodule\n"
      "config c; design top; instance top.a1 use #(.W(P)); endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 20);
}

TEST(ConfigParamApply, ChildOverrideSeesTheParentsOverriddenValue) {
  ElabFixture f;
  auto* design =
      ConfigElab(f,
                 "module adder #(parameter W = 8); endmodule\n"
                 "module top; parameter WIDTH = 16; adder a1(); endmodule\n"
                 "config cfg1;\n"
                 "  design top;\n"
                 "  instance top use #(.WIDTH(32));\n"
                 "  instance top.a1 use #(.W(top.WIDTH));\n"
                 "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* a1 = ChildAt(design->top_modules[0], 0);
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(ResolvedParam(design->top_modules[0], "WIDTH"), 32);
  EXPECT_EQ(ResolvedParam(a1, "W"), 32);
}

TEST(ConfigParamApply, DISABLED_AnUpwardNameReachesASiblingOfTheParent) {
  ElabFixture f;
  auto* design =
      ConfigElab(f,
                 "module leaf #(parameter W = 1); endmodule\n"
                 "module mid #(parameter P = 1); leaf b(); endmodule\n"
                 "module top; mid #(.P(9)) a2(); mid a1(); endmodule\n"
                 "config cfg;\n"
                 "  design top;\n"
                 "  instance top.a1.b use #(.W(a2.P));\n"
                 "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* b = ChildAt(ChildAt(design->top_modules[0], 1), 0);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(ResolvedParam(b, "W"), 9);
}

void ExpectBindInvisibleNameRejected(const std::string& src, uint32_t line) {
  ElabFixture f;
  ConfigElab(f, src);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be named by a bind statement", line,
                            "33.4.3"));
}

TEST(ConfigParamOverride, DISABLED_AWildcardCandidateNotYetImportedRejected) {
  ExpectBindInvisibleNameRejected(
      "package p; parameter K = 5; endpackage\n"
      "module adder #(parameter W = 8); endmodule\n"
      "module top; import p::*; adder a1(); endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(K));\n"
      "endconfig\n",
      6);
}

TEST(ConfigParamOverride, AWildcardCandidateAlreadyImportedAccepted) {
  ElabFixture f;
  auto* a1 = ConfigElabFirstChild(
      f,
      "package p; parameter K = 5; endpackage\n"
      "module adder #(parameter W = 8); endmodule\n"
      "module top; import p::*; localparam L = K; adder a1(); endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(K));\n"
      "endconfig\n");
  ASSERT_NE(a1, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(a1, "W"), 5);
}

TEST(ConfigParamOverride, DISABLED_ANameDeclaredOnlyInTheUnitRejected) {
  ExpectBindInvisibleNameRejected(
      "parameter CU_P = 5;\n"
      "module adder #(parameter W = 8); endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(CU_P));\n"
      "endconfig\n",
      6);
}

TEST(ConfigParamOverride, DISABLED_AParameterOfABoundInstanceRejected) {
  ExpectBindInvisibleNameRejected(
      "module adder #(parameter W = 8); endmodule\n"
      "module mon #(parameter P = 3); endmodule\n"
      "module top; adder a1(); endmodule\n"
      "bind top mon m();\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(top.m.P));\n"
      "endconfig\n",
      7);
}

TEST(ConfigParamOverride, DISABLED_AParameterOfAnOrdinaryInstanceAccepted) {
  ElabFixture f;
  auto* design = ConfigElab(f,
                            "module adder #(parameter W = 8); endmodule\n"
                            "module mon #(parameter P = 3); endmodule\n"
                            "module top; adder a1(); mon m(); endmodule\n"
                            "config c;\n"
                            "  design top;\n"
                            "  instance top.a1 use #(.W(top.m.P));\n"
                            "endconfig\n");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(ChildAt(design->top_modules[0], 0), "W"), 3);
}

}  // namespace
