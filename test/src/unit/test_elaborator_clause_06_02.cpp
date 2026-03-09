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

TEST(DataTypesAndObjects, TwoStateVariableType) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  bit [15:0] b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "b") {
      EXPECT_EQ(v.width, 16u);
      EXPECT_FALSE(v.is_4state);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(DataTypesAndObjects, IntVariableIsDataObject) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  int i;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "i") {
      EXPECT_EQ(v.width, 32u);
      EXPECT_FALSE(v.is_4state);
      EXPECT_TRUE(v.is_signed);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(DataTypesAndObjects, RealVariableIsDataObject) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  real r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "r") {
      EXPECT_TRUE(v.is_real);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(DataTypesAndObjects, StringVariableIsDataObject) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  string s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "s") {
      EXPECT_TRUE(v.is_string);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(DataTypesAndObjects, DifferentNetTypesAreDataObjects) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  tri tr;\n"
      "  wand wa;\n"
      "  wor wo;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 4u);
  bool found_w = false, found_tr = false, found_wa = false, found_wo = false;
  for (const auto& n : mod->nets) {
    if (n.name == "w") {
      EXPECT_EQ(n.net_type, NetType::kWire);
      found_w = true;
    }
    if (n.name == "tr") {
      EXPECT_EQ(n.net_type, NetType::kTri);
      found_tr = true;
    }
    if (n.name == "wa") {
      EXPECT_EQ(n.net_type, NetType::kWand);
      found_wa = true;
    }
    if (n.name == "wo") {
      EXPECT_EQ(n.net_type, NetType::kWor);
      found_wo = true;
    }
  }
  EXPECT_TRUE(found_w);
  EXPECT_TRUE(found_tr);
  EXPECT_TRUE(found_wa);
  EXPECT_TRUE(found_wo);
}

}  // namespace
