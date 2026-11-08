#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_child_instance.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ParameterDependence, LocalparamUpdatesWhenParamOverridden) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "  localparam int MASK = (1 << W) - 1;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(8)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  for (const auto& p : child->params) {
    if (p.name == "MASK") {
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 255);
    }
  }
}

TEST(ParameterDependence, OverridePropagatesThroughDependencyChain) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3,\n"
      "               parameter int C = B + 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.A(5)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectResolvedParams(SoleChildInstance(design),
                       {{"A", 5}, {"B", 15}, {"C", 16}});
}

TEST(ParameterDependence, OrderedListOverridePropagatesThroughDependencyChain) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3,\n"
      "               parameter int C = B + 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(5) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectResolvedParams(SoleChildInstance(design),
                       {{"A", 5}, {"B", 15}, {"C", 16}});
}

TEST(ParameterDependence, OverrideOfNonDependencyLeavesIndependentUnchanged) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 7,\n"
      "               parameter int B = 9)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.A(100)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].resolved_value, 100);
  EXPECT_EQ(u0->params[1].resolved_value, 9);
}

TEST(ParameterDependence, DefparamOverridePropagatesThroughDependencyChain) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3,\n"
      "               parameter int C = B + 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.A = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
  EXPECT_EQ(u0->params[1].resolved_value, 15);
  EXPECT_EQ(u0->params[2].resolved_value, 16);
}

TEST(ParameterDependence, DependentParamOwnInstanceOverrideBeatsSourceParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.A(5), .B(100)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
  EXPECT_EQ(u0->params[1].resolved_value, 100);
}

TEST(ParameterDependence, DependentParamOwnDefparamOverrideBeatsSourceParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = A * 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.A = 5;\n"
      "  defparam u0.B = 100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
  EXPECT_EQ(u0->params[1].resolved_value, 100);
}

TEST(ParameterDependence, RangeDependencyRecomputesOnOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter P = 1,\n"
      "               parameter [P:0] Q = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[1].name, "Q");
  EXPECT_EQ(u0->params[1].decl_width, 8u);
}

TEST(ParameterDependence, TypeParamOverrideRecomputesDependentVariableWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte,\n"
      "               parameter T p = 7)();\n"
      "  T x;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(shortint)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_GE(u0->variables.size(), 1u);
  EXPECT_EQ(u0->variables[0].name, "x");
  EXPECT_EQ(u0->variables[0].width, 16u);
}

TEST(ParameterDependence, TypeOverrideToClassMakesDependentAssignmentIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "endclass\n"
      "module child #(parameter type T = int,\n"
      "               parameter T p = 7)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(C)) u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "cannot assign an integral value to parameter whose type "
                    "parameter 'T' resolved to a class type",
                    4, "23.10.3"));
}

TEST(ParameterDependence, UnoverriddenClassTypeDefaultFailsElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "endclass\n"
      "module child #(parameter type T = C,\n"
      "               parameter T p = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "cannot assign an integral value to parameter whose type "
                    "parameter 'T' resolved to a class type",
                    4, "23.10.3"));
}

TEST(ParameterDependence, TypeOverrideToIntegralMakesClassDefaultLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "endclass\n"
      "module child #(parameter type T = C,\n"
      "               parameter T p = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(int)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParameterDependence, NoDefaultTypeParamWithDependentRequiresOverride) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter type T2,\n"
      "               parameter T2 p2 = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "type parameter 'T2' of 'child' has no default type and no "
                    "override at instantiation",
                    5, "6.20.1"));
}

TEST(ParameterDependence,
     NoDefaultTypeParamSizesDependentParamFromOverrideType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T2,\n"
      "               parameter T2 p2 = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T2(byte)) u_byte();\n"
      "  child #(.T2(shortint)) u_short();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 2u);
  auto width_of_p2 = [](const auto* inst) -> uint32_t {
    for (const auto& p : inst->params) {
      if (p.name == "p2") return p.decl_width;
    }
    return 0;
  };
  auto* u_byte = design->top_modules[0]->children[0].resolved;
  auto* u_short = design->top_modules[0]->children[1].resolved;
  ASSERT_NE(u_byte, nullptr);
  ASSERT_NE(u_short, nullptr);
  EXPECT_EQ(width_of_p2(u_byte), 8u);
  EXPECT_EQ(width_of_p2(u_short), 16u);
}

}  // namespace
