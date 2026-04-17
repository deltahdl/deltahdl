#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ModuleInstanceParameterAssignment, OverrideSuppliesValueToInstanceParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(8)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 8);
}

TEST(ModuleInstanceParameterAssignment, UnknownParameterNameProducesError) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.NOPE(8)) u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ModuleInstanceParameterAssignment, PartialOverrideLeavesUnspecifiedAtDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1,\n"
      "               parameter int B = 2,\n"
      "               parameter int C = 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.B(20)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 1);
  EXPECT_EQ(u0->params[1].name, "B");
  EXPECT_EQ(u0->params[1].resolved_value, 20);
  EXPECT_EQ(u0->params[2].name, "C");
  EXPECT_EQ(u0->params[2].resolved_value, 3);
}

TEST(ModuleInstanceParameterAssignment, EmptyExpressionRetainsDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 7)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W()) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_EQ(u0->params[0].resolved_value, 7);
}

TEST(ModuleInstanceParameterAssignment, DifferentInstancesMayUseDifferentMethods) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(8) u_ordered();\n"
      "  child #(.W(8)) u_named();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  auto* u_ordered = top->children[0].resolved;
  auto* u_named = top->children[1].resolved;
  ASSERT_NE(u_ordered, nullptr);
  ASSERT_NE(u_named, nullptr);
  ASSERT_EQ(u_ordered->params.size(), 1u);
  ASSERT_EQ(u_named->params.size(), 1u);
  EXPECT_EQ(u_ordered->params[0].resolved_value, 8);
  EXPECT_EQ(u_named->params[0].resolved_value, 8);
}

}  // namespace
