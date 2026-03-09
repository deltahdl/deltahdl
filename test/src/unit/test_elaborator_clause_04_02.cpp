#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabCh42, SingleModuleDesignHasOneTopModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(ElabCh42, TopModuleRegisteredInAllModulesMap) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("top");
  ASSERT_NE(it, design->all_modules.end());
  EXPECT_EQ(it->second, design->top_modules[0]);
}

TEST(ElabCh42, HierarchicalDesignElaboratesChildModules) {
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

TEST(ElabCh42, ChildModuleResolvedPointerIsNotNull) {
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

TEST(ElabCh42, ChildModuleAppearsInAllModulesMap) {
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
  auto it = design->all_modules.find("child");
  EXPECT_NE(it, design->all_modules.end());
}

TEST(ElabCh42, MultipleInstancesOfSameModule) {
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

TEST(ElabCh42, EmptyModuleElaboratesWithNoPorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module empty;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_TRUE(mod->ports.empty());
  EXPECT_TRUE(mod->processes.empty());
  EXPECT_TRUE(mod->assigns.empty());
  EXPECT_TRUE(mod->children.empty());
}

TEST(ElabCh42, ModuleWithPortsElaboratesPorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
}

TEST(ElabCh42, UnresolvedModuleNameProducesError) {
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

TEST(ElabCh42, DesignWithVariablesAndProcesses) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic clk;\n"
      "  logic [7:0] count;\n"
      "  initial count = 0;\n"
      "  always_ff @(posedge clk) count <= count + 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->variables.size(), 2u);
  EXPECT_EQ(mod->processes.size(), 2u);
}

TEST(ElabCh42, ElaborateSpecificTopModuleByName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "a");
}

TEST(ElabCh42, PortBindingInHierarchicalInstance) {
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

TEST(ElabCh42, DeepHierarchyThreeLevels) {
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

TEST(ElabCh42, ModuleUsedAtMultipleLevels) {
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

TEST(ElabCh42, TwoIndependentTopModules) {
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

}  // namespace
