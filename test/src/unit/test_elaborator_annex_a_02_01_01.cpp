#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParameterDeclElaboration, ParameterResolvesValue) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "WIDTH") {
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 8);
      EXPECT_FALSE(p.is_localparam);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParameterDeclElaboration, MultipleParametersResolve) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int A = 1, B = 2, C = 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int resolved_count = 0;
  for (const auto& p : mod->params) {
    if (p.name == "A" || p.name == "B" || p.name == "C") {
      EXPECT_TRUE(p.is_resolved);
      resolved_count++;
    }
  }
  EXPECT_EQ(resolved_count, 3);
}

TEST(ParameterDeclElaboration, ParameterExpressionEvaluated) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int HALF = 16 / 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "HALF") {
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 8);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
