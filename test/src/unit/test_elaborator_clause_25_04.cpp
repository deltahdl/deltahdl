// §25.4

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(InterfacePorts, SimpleBusWithClkPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "  logic [1:0] mode;\n"
      "  logic start, rdy;\n"
      "endinterface\n",
      f, "simple_bus");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterfacePorts, InterfaceWithOutputPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc(output logic done);\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].direction, Direction::kOutput);
}

TEST(InterfacePorts, InterfaceWithInoutPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface i1(input a, output b, inout c);\n"
      "  wire d;\n"
      "endinterface\n",
      f, "i1");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ASSERT_EQ(design->top_modules[0]->ports.size(), 3u);
  EXPECT_EQ(design->top_modules[0]->ports[2].direction, Direction::kInout);
}

TEST(InterfacePorts, TwoInstancesShareExternalWire) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf1(clk);\n"
      "  simple_bus sb_intf2(clk);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[0].module_name, "simple_bus");
  EXPECT_EQ(top->children[0].inst_name, "sb_intf1");
  EXPECT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[1].module_name, "simple_bus");
  EXPECT_EQ(top->children[1].inst_name, "sb_intf2");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

}  // namespace
