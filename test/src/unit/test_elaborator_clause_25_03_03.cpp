#include "fixture_elaborator.h"

namespace {

TEST(GenericInterfaceReference, MultipleGenericPortsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module cpuMod(interface d, interface j);\n"
      "endmodule\n",
      f, "cpuMod");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
}

TEST(GenericInterfaceReference, NamedConnectionBindsGenericInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req;\n"
      "endinterface\n"
      "module memMod(interface a, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(.a(sb_intf), .clk(clk));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[1].module_name, "memMod");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

TEST(GenericInterfaceReference, PartialImplicitWithNamedGenericInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req;\n"
      "endinterface\n"
      "module memMod(interface a, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(.*, .a(sb_intf));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[1].module_name, "memMod");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

TEST(GenericInterfaceReference, ImplicitOnlyCannotReferenceGenericInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req;\n"
      "endinterface\n"
      "module memMod(interface a, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus a();\n"
      "  memMod mem(.*);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(GenericInterfaceReference, FullExampleEndToEnd) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module memMod(interface a, input logic clk);\n"
      "endmodule\n"
      "module cpuMod(interface b, input logic clk);\n"
      "endmodule\n"
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "  logic [1:0] mode;\n"
      "  logic start, rdy;\n"
      "endinterface: simple_bus\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(.a(sb_intf), .clk(clk));\n"
      "  cpuMod cpu(.b(sb_intf), .clk(clk));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 3u);
  EXPECT_EQ(top->children[0].module_name, "simple_bus");
  EXPECT_EQ(top->children[1].module_name, "memMod");
  EXPECT_EQ(top->children[2].module_name, "cpuMod");
}

}  // namespace
