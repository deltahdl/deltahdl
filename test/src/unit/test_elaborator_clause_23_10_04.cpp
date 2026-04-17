// §23.10.4

#include "fixture_elaborator.h"

namespace {

TEST(BuildingBlockElaboration, AllModulesMapPopulated) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_NE(design->all_modules.find("top"), design->all_modules.end());
  EXPECT_NE(design->all_modules.find("child"), design->all_modules.end());
}

TEST(BuildingBlockElaboration, HierarchicalDesignElaboratesChildModules) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "child");
  EXPECT_EQ(top->children[0].inst_name, "c1");
}

TEST(BuildingBlockElaboration, ChildModuleResolvedPointerIsNotNull) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_NE(top->children[0].resolved, nullptr);
}

TEST(BuildingBlockElaboration, MultipleInstancesOfSameModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  child c2();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  EXPECT_EQ(top->children[0].inst_name, "c1");
  EXPECT_EQ(top->children[1].inst_name, "c2");
}

TEST(BuildingBlockElaboration, UnresolvedModuleNameProducesError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  nonexistent n1();\n"
      "endmodule\n",
      f);

  if (design != nullptr) {
    EXPECT_TRUE(f.has_errors);
  }
}

TEST(BuildingBlockElaboration, PortBindingInHierarchicalInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child c1(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_GE(top->children[0].port_bindings.size(), 2u);
}

TEST(BuildingBlockElaboration, DeepHierarchyThreeLevels) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_NE(top->children[0].resolved, nullptr);
  auto* mid = top->children[0].resolved;
  ASSERT_EQ(mid->children.size(), 1u);
  EXPECT_EQ(mid->children[0].module_name, "leaf");
}

TEST(BuildingBlockElaboration, ModuleUsedAtMultipleLevels) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module shared;\n"
      "endmodule\n"
      "module mid;\n"
      "  shared s1();\n"
      "endmodule\n"
      "module top;\n"
      "  shared s2();\n"
      "  mid m1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("shared");
  EXPECT_NE(it, design->all_modules.end());
}

TEST(BuildingBlockElaboration, TwoIndependentTopModules) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->all_modules.count("a"), 1u);
  EXPECT_EQ(design->all_modules.count("b"), 1u);
}

TEST(BuildingBlockElaboration, InstanceParameterValueResolvedAfterElaboration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 4);
}

TEST(BuildingBlockElaboration, NestedInstanceParameterValuesResolved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf #(parameter int L = 2)();\n"
      "endmodule\n"
      "module mid #(parameter int M = 3)();\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mid = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(mid, nullptr);
  ASSERT_EQ(mid->params.size(), 1u);
  EXPECT_TRUE(mid->params[0].is_resolved);
  EXPECT_EQ(mid->params[0].resolved_value, 3);
  auto* leaf = mid->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  ASSERT_EQ(leaf->params.size(), 1u);
  EXPECT_TRUE(leaf->params[0].is_resolved);
  EXPECT_EQ(leaf->params[0].resolved_value, 2);
}

}  // namespace
