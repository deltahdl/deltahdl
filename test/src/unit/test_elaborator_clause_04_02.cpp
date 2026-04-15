#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(HardwareModelExecutionElaboration, TopModuleRegisteredInAllModulesMap) {
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

TEST(HardwareModelExecutionElaboration, HierarchicalDesignElaboratesChildModules) {
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

TEST(HardwareModelExecutionElaboration, ChildModuleResolvedPointerIsNotNull) {
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

TEST(HardwareModelExecutionElaboration, ChildModuleAppearsInAllModulesMap) {
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

TEST(HardwareModelExecutionElaboration, MultipleInstancesOfSameModule) {
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

TEST(HardwareModelExecutionElaboration, EmptyModuleElaboratesWithNoPorts) {
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

TEST(HardwareModelExecutionElaboration, ModuleWithPortsElaboratesPorts) {
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

TEST(HardwareModelExecutionElaboration, UnresolvedModuleNameProducesError) {
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

TEST(HardwareModelExecutionElaboration, DesignWithVariablesAndProcesses) {
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

TEST(HardwareModelExecutionElaboration, PortBindingInHierarchicalInstance) {
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

TEST(HardwareModelExecutionElaboration, DeepHierarchyThreeLevels) {
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

TEST(HardwareModelExecutionElaboration, ModuleUsedAtMultipleLevels) {
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

TEST(HardwareModelExecutionElaboration, TwoIndependentTopModules) {
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
