#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParameterizedInterface, DefaultParameterUsedWhenNotOverridden) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 8);
}

TEST(ParameterizedInterface, PositionalOverrideAppliedToInterfaceInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(16) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 16);
}

TEST(ParameterizedInterface, NamedOverrideAppliedToInterfaceInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.WIDTH(32)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "WIDTH");
  EXPECT_EQ(u0->params[0].resolved_value, 32);
}

TEST(ParameterizedInterface, TwoInstancesGetIndependentOverrideValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(4) narrow();\n"
      "  ifc #(.WIDTH(16)) wide();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->children.size(), 2u);
  auto* narrow = design->top_modules[0]->children[0].resolved;
  auto* wide = design->top_modules[0]->children[1].resolved;
  ASSERT_NE(narrow, nullptr);
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(narrow->params[0].resolved_value, 4);
  EXPECT_EQ(wide->params[0].resolved_value, 16);
}

TEST(ParameterizedInterface, MultipleParametersOverriddenByName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int A = 2, parameter int B = 3);\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.B(30), .A(20)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 20);
  EXPECT_EQ(u0->params[1].name, "B");
  EXPECT_EQ(u0->params[1].resolved_value, 30);
}

TEST(ParameterizedInterface, EmptyParamListUsesDefaults) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 5);\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #() u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
}

TEST(ParameterizedInterface, OverrideExpressionEvaluatedInParentScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 1);\n"
      "endinterface\n"
      "module top;\n"
      "  parameter int N = 7;\n"
      "  ifc #(.WIDTH(N + 1)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 8);
}

TEST(ParameterizedInterface, UnknownNamedParameterIsError) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.BOGUS(16)) u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
