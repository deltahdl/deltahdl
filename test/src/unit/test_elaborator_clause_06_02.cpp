#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DataTypesAndObjects, VariableIsDataObject) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [7:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "v");
  EXPECT_EQ(mod->variables[0].width, 8u);
  EXPECT_TRUE(mod->variables[0].is_4state);
}

TEST(DataTypesAndObjects, NetIsDataObject) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire [3:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "w");
  EXPECT_EQ(mod->nets[0].width, 4u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWire);
}

TEST(DataTypesAndObjects, ParameterIsDataObject) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  parameter WIDTH = 8;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->params.size(), 1u);
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "WIDTH") {
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 8);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(DataTypesAndObjects, TypeDeclaresMultipleObjects) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  bool found_a = false, found_b = false, found_c = false;
  for (const auto& v : mod->variables) {
    if (v.name == "a") found_a = true;
    if (v.name == "b") found_b = true;
    if (v.name == "c") found_c = true;
  }
  EXPECT_TRUE(found_a);
  EXPECT_TRUE(found_b);
  EXPECT_TRUE(found_c);
}

TEST(DataTypesAndObjects, TypedefCreatesUserDefinedType) {
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

}  // namespace
