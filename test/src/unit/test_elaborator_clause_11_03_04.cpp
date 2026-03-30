#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StateOps, IntElaboratesAs2State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->variables[0].is_4state);
}

TEST(StateOps, BitElaboratesAs2State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->variables[0].is_4state);
}

TEST(StateOps, LogicElaboratesAs4State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_4state);
}

TEST(StateOps, IntegerElaboratesAs4State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_4state);
}

TEST(StateOps, ByteElaboratesAs2State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->variables[0].is_4state);
}

TEST(StateOps, MixedStateVarsElaborateCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  integer b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 2u);
  bool found_2state = false;
  bool found_4state = false;
  for (const auto& v : mod->variables) {
    if (v.name == "a") {
      EXPECT_FALSE(v.is_4state);
      found_2state = true;
    }
    if (v.name == "b") {
      EXPECT_TRUE(v.is_4state);
      found_4state = true;
    }
  }
  EXPECT_TRUE(found_2state);
  EXPECT_TRUE(found_4state);
}

}  // namespace
