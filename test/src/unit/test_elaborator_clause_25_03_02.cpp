// §25.3.2

#include "fixture_elaborator.h"

namespace {

TEST(InterfaceNamedBundle, InterfaceWithVariablesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterfaceNamedBundle, ModuleWithInterfacePortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "  logic avail;\n"
      "  always @(posedge a.clk) a.gnt <= a.req & avail;\n"
      "endmodule\n",
      f, "memMod");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterfaceNamedBundle, TopBindsInterfaceToModulePositionally) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus a, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf, clk);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  EXPECT_EQ(top->children[0].module_name, "simple_bus");
  EXPECT_EQ(top->children[0].inst_name, "sb_intf");
  EXPECT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[1].module_name, "memMod");
  EXPECT_EQ(top->children[1].inst_name, "mem");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

TEST(InterfaceNamedBundle, TopBindsInterfaceToModuleByName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req;\n"
      "endinterface\n"
      "module cpuMod(simple_bus b, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  cpuMod cpu(.b(sb_intf), .clk(clk));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[1].module_name, "cpuMod");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

TEST(InterfaceNamedBundle, TopBindsInterfaceToModuleImplicitly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req;\n"
      "endinterface\n"
      "module memMod(simple_bus sb_intf, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(.*);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[1].module_name, "memMod");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

}  // namespace
