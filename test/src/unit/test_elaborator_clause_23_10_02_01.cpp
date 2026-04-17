#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(OrderedListParameterAssignment, PositionalValuesMapInDeclarationOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10, 15) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 10);
  EXPECT_EQ(u0->params[1].name, "B");
  EXPECT_EQ(u0->params[1].resolved_value, 15);
}

TEST(OrderedListParameterAssignment, SinglePositionalValueOverridesFirstParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(42) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 42);
}

TEST(OrderedListParameterAssignment, PartialSubsetKeepsTrailingParametersAtDeclaredDefaults) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2,\n"
      "               parameter int B = 3,\n"
      "               parameter int C = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  EXPECT_EQ(u0->params[0].resolved_value, 10);
  EXPECT_EQ(u0->params[1].resolved_value, 3);
  EXPECT_EQ(u0->params[2].resolved_value, 4);
}

TEST(OrderedListParameterAssignment, EmptyOrderedListKeepsAllDeclaredDefaults) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 7,\n"
      "               parameter int B = 9)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #() u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].resolved_value, 7);
  EXPECT_EQ(u0->params[1].resolved_value, 9);
}

TEST(OrderedListParameterAssignment, TooManyPositionalValuesRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(10, 15) u0();\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(f.has_errors);
}

TEST(OrderedListParameterAssignment, LocalparamInParameterPortListExcludedFromOrderedList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1,\n"
      "               localparam int L = 10,\n"
      "               parameter int B = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(5, 6) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  for (const auto& p : u0->params) {
    if (p.name == "A") {
      EXPECT_FALSE(p.is_localparam);
      EXPECT_EQ(p.resolved_value, 5);
    } else if (p.name == "L") {
      EXPECT_TRUE(p.is_localparam);
      EXPECT_EQ(p.resolved_value, 10);
    } else if (p.name == "B") {
      EXPECT_FALSE(p.is_localparam);
      EXPECT_EQ(p.resolved_value, 6);
    }
  }
}

TEST(OrderedListParameterAssignment, OrderedListCountedAgainstNonLocalparamsOnly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1,\n"
      "               localparam int L = 99,\n"
      "               parameter int B = 2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(7, 8, 9) u0();\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
