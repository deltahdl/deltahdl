#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LogicValuesElab, LogicScalarVariableIs4State) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "v");
  EXPECT_EQ(mod->variables[0].width, 1u);
  EXPECT_TRUE(mod->variables[0].is_4state);
}

TEST(LogicValuesElab, LogicVectorVariableIs4State) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [3:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
  EXPECT_TRUE(mod->variables[0].is_4state);
}

TEST(LogicValuesElab, UserTypeBuiltFromLogicInheritsFourState) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "x") {
      EXPECT_EQ(v.width, 8u);
      EXPECT_TRUE(v.is_4state);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(LogicValuesElab, TwoStateTypeStoresOnlyZeroOrOne) {
  // §6.3.1: some data types are 2-state and store only 0 or 1 in each bit,
  // in contrast to the 4-state logic type. A 2-state declaration such as
  // bit must therefore be classified as not 4-state by the elaborator.
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  bit b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "b");
  EXPECT_EQ(mod->variables[0].width, 1u);
  EXPECT_FALSE(mod->variables[0].is_4state);
}

TEST(LogicValuesElab, EventTypeIsNotFourState) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  event e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "e");
  EXPECT_TRUE(mod->variables[0].is_event);
  EXPECT_FALSE(mod->variables[0].is_4state);
}

TEST(LogicValuesElab, RealTypeIsNotFourState) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  real r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "r");
  EXPECT_TRUE(mod->variables[0].is_real);
  EXPECT_FALSE(mod->variables[0].is_4state);
}

}  // namespace
