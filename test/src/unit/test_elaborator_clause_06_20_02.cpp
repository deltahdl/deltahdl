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

TEST(PrimaryElaboration, ConstantPrimaryRealLiteral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter real R = 3.14;\n"
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

}  // namespace
