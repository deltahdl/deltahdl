#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ModuleInstanceParameterAssignment, LocalparamUpdatesWhenParamOverridden) {
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

TEST(ModuleInstanceParameterAssignment, OverridePropagatesThroughDependencyChain) {
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
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 5);
  EXPECT_EQ(u0->params[1].name, "B");
  EXPECT_EQ(u0->params[1].resolved_value, 15);
  EXPECT_EQ(u0->params[2].name, "C");
  EXPECT_EQ(u0->params[2].resolved_value, 16);
}

TEST(ModuleInstanceParameterAssignment, OverrideOfNonDependencyLeavesIndependentUnchanged) {
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

}  // namespace
