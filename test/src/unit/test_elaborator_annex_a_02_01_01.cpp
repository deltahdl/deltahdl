#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_localparam_resolution.h"

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

TEST(ParameterDeclElaboration, LocalparamResolvesAsLocal) {
  ElabFixture f;
  ExpectLocalparamDepth32ResolvesAsLocal(f);
}

// A.2.1.1's parameter declarations take a data_type_or_implicit, which
// A.2.2.1 lets be a type_reference (§6.23): V is of W's type and P of x's,
// each four bits, so 5'h1F converts to 15 in both, where an untyped parameter
// would hold 31.
TEST(ParameterDeclElaboration, ValueParametersOfATypeReferenceTakeTheType) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m #(parameter logic [3:0] W = 4,\n"
      "           parameter type(W) V = 5'h1F);\n"
      "  logic [3:0] x;\n"
      "  localparam type(x) P = 5'h1F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  int found = 0;
  for (const auto& p : design->top_modules[0]->params) {
    if (p.name != "V" && p.name != "P") continue;
    EXPECT_EQ(p.decl_width, 4u) << p.name;
    EXPECT_EQ(p.resolved_value, 15) << p.name;
    ++found;
  }
  EXPECT_EQ(found, 2);
}

}  // namespace
