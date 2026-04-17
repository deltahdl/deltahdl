#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParameterOverride, DefparamBeatsInstanceParameterAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.WIDTH(8)) u0();\n"
      "  defparam u0.WIDTH = 16;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 16);
}

TEST(ParameterOverride, DefparamBeatsOrderedInstanceParameterAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(8) u0();\n"
      "  defparam u0.WIDTH = 24;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 24);
}

TEST(ParameterOverride, UntypedUnrangedAdoptsOverrideValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter P = 3'h2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = 1000;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 1000);
}

TEST(ParameterOverride, RangedUntypedTruncatesOverrideToDeclarationRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter [2:0] P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = 13;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
}

TEST(ParameterOverride, TypedUnrangedConvertsOverrideToDeclarationType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = 64'h1_0000_0001;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 1);
}

TEST(ParameterOverride, SignedRangedKeepsDeclarationRangeAndSignedness) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter signed [3:0] P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = 17;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 1);
}

}  // namespace
