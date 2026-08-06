

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

// §25.4 draws the line between the nets/variables in an interface's port list
// and the other nets/variables declared inside it: only those in the port list
// can be connected externally, by name or position, when the interface is
// instantiated. This is the accepting half — a name that IS in the port list
// (clk) connects with no diagnostic.
TEST(InterfacePorts, PortListNameConnectsWithoutWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module top;\n"
      "  logic c = 0;\n"
      "  simple_bus sb(.clk(c));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §25.4 rejecting half: `req` is declared inside the interface but is NOT in
// its port list, so it cannot be connected externally. The elaborator, matching
// an external named connection only against the interface's port list, flags
// the
// `.req` connection as a non-port target while the sibling `.clk` (a real port)
// stays clean — exhibiting the port-list-vs-internal-net distinction. The
// connection is diagnosed but not fatal, so the design still elaborates.
TEST(InterfacePorts, InternalNetNotConnectableExternally) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module top;\n"
      "  logic c = 0;\n"
      "  simple_bus sb(.clk(c), .req(c));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §25.4 (i1 example): the input, output, and inout wires of an interface port
// list can each be individually connected to the interface when it is
// instantiated. External connection of the port-list nets is what §25.4 permits
// regardless of direction, so drive the LRM's three-direction interface through
// elaboration and connect every port by name, confirming each binding resolves
// to a port of the expected direction with no diagnostic. Prior tests only
// connected an input port externally; this covers the output and inout forms.
TEST(InterfacePorts, AllPortDirectionsConnectedExternally) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface i1(input a, output b, inout c);\n"
      "  wire d;\n"
      "endinterface\n"
      "module top;\n"
      "  wire aw, bw, cw;\n"
      "  i1 u(.a(aw), .b(bw), .c(cw));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  const auto& inst = top->children[0];
  ASSERT_NE(inst.resolved, nullptr);
  EXPECT_EQ(inst.port_bindings.size(), 3u);
  ASSERT_EQ(inst.resolved->ports.size(), 3u);
  EXPECT_EQ(inst.resolved->ports[0].direction, Direction::kInput);
  EXPECT_EQ(inst.resolved->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(inst.resolved->ports[2].direction, Direction::kInout);
}

// §25.4 ties interface port declaration syntax and semantics to those of
// modules (§23.2.2), which includes the non-ANSI form where the header names
// the ports and body declarations supply their directions. A non-ANSI
// interface's ports are still externally connectable, so build one from
// §23.2.2's non-ANSI syntax and instantiate it with named connections,
// confirming the folded ports resolve as connection targets through the full
// pipeline.
TEST(InterfacePorts, NonAnsiInterfacePortsConnectExternally) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc(clk, rst);\n"
      "  input logic clk;\n"
      "  input logic rst;\n"
      "endinterface\n"
      "module top;\n"
      "  logic c = 0, r = 0;\n"
      "  ifc u(.clk(c), .rst(r));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  const auto& inst = top->children[0];
  ASSERT_NE(inst.resolved, nullptr);
  EXPECT_EQ(inst.port_bindings.size(), 2u);
  ASSERT_EQ(inst.resolved->ports.size(), 2u);
  EXPECT_EQ(inst.resolved->ports[0].direction, Direction::kInput);
  EXPECT_EQ(inst.resolved->ports[1].direction, Direction::kInput);
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
