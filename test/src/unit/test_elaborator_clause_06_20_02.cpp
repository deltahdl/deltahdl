#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ExpressionElaboration, ConstantBinaryExprInParamElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int WIDTH = 4 + 4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, ConstantPrimaryIntegerLiteral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, ConstantPrimaryParameterRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = 5;\n"
      "  parameter int B = A;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, ParameterDependsOnEarlier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  parameter int MASK = (1 << WIDTH) - 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, ParameterSignedRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter signed [3:0] mux_selector = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, MultipleParamsOneDeclLine) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter e = 25, f = 9;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, RealParameter) {
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

TEST(ValueParameters, UntypedParameterResolvesValue) {
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
  EXPECT_EQ(p.resolved_value, 42);
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

}  // namespace
