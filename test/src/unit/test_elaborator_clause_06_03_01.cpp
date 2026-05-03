#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.3.1 ¶4: a `logic` declaration produces an object of the basic 4-state
// data type. The elaborated variable must carry is_4state=true.
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

// §6.3.1 ¶4 + ¶5: a vector declared from `logic` is a 4-state vector — every
// bit of the resulting variable is part of the 4-state storage.
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

// §6.3.1 ¶4: a user-defined data type constructed from `logic` (via typedef)
// must inherit the 4-state property from its base.
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

// §6.3.1 ¶5: "Other exceptions are the event type (see 6.17), which has no
// storage." The elaborator must mark an event-typed variable as is_event,
// distinguishing it from the 4-state/2-state value-storing categories.
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

// §6.3.1 ¶5: "Other exceptions are ... the real types (see 6.12)." The
// elaborator must mark a real variable as is_real and not as a 4-state value.
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
