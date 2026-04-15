
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- R1: An interface port instance shall always be connected to an interface
//     instance or a higher level interface port ---

TEST(InterfacePortConnectionRulesElaboration,
     GenericInterfacePortConnectedToInterfaceInstance) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(interface port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(.port_a(inst));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     InterfacePortConnectedToHigherLevelInterfacePort) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(interface port_a);\n"
             "endmodule\n"
             "module mid(interface port_b);\n"
             "  child u(.port_a(port_b));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     InterfacePortConnectedToNetErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(interface port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.port_a(w));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfacePortConnectionRulesElaboration,
     InterfacePortConnectedToVariableErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(interface port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x;\n"
      "  child u(.port_a(x));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfacePortConnectionRulesElaboration,
     InterfacePortConnectedToExpressionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(interface port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x;\n"
      "  child u(.port_a(x + 1));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// --- R2: An interface port cannot be left unconnected ---

TEST(InterfacePortConnectionRulesElaboration,
     UnconnectedInterfacePortEmptyListErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(interface port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfacePortConnectionRulesElaboration,
     UnconnectedInterfacePortOmittedByNameErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(interface port_a, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  bus_if inst();\n"
      "  child u(.clk(clk));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfacePortConnectionRulesElaboration,
     UnconnectedInterfacePortPositionalBlankErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(interface port_a, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk;\n"
      "  child u(, clk);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfacePortUnconnectedErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(bus_if port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// --- R3: If a port declaration has a generic interface type, then it can be
//     connected to an interface instance of any type ---

TEST(InterfacePortConnectionRulesElaboration,
     GenericInterfacePortAcceptsAnyInterfaceTypeA) {
  EXPECT_TRUE(
      ElabOk("interface axi_if;\n"
             "  logic [31:0] addr;\n"
             "endinterface\n"
             "module child(interface port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  axi_if inst();\n"
             "  child u(.port_a(inst));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     GenericInterfacePortAcceptsAnyInterfaceTypeB) {
  EXPECT_TRUE(
      ElabOk("interface apb_if;\n"
             "  logic [15:0] paddr;\n"
             "endinterface\n"
             "module child(interface port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  apb_if inst();\n"
             "  child u(.port_a(inst));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     GenericInterfaceWithModportAcceptsAnyType) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "endinterface\n"
             "module child(interface.master port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(.port_a(inst));\n"
             "endmodule\n"));
}

// --- R4: If a port declaration has a named interface type, then it shall be
//     connected to an interface instance of the identical type ---

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfacePortConnectedToSameType) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(bus_if port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(.port_a(inst));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfacePortConnectedToDifferentTypeErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "interface other_if;\n"
      "  logic data;\n"
      "endinterface\n"
      "module child(bus_if port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  other_if inst();\n"
      "  child u(.port_a(inst));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfaceWithModportConnectedToSameType) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "  modport slave(input data);\n"
             "endinterface\n"
             "module child(bus_if.slave port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(.port_a(inst));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfaceWithModportConnectedToDifferentTypeErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "  modport slave(input data);\n"
      "endinterface\n"
      "interface other_if;\n"
      "  logic data;\n"
      "  modport slave(input data);\n"
      "endinterface\n"
      "module child(bus_if.slave port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  other_if inst();\n"
      "  child u(.port_a(inst));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// --- Edge cases ---

TEST(InterfacePortConnectionRulesElaboration,
     MultipleInterfacePortsAllConnected) {
  EXPECT_TRUE(
      ElabOk("interface axi_if;\n"
             "  logic [31:0] addr;\n"
             "endinterface\n"
             "interface apb_if;\n"
             "  logic [15:0] paddr;\n"
             "endinterface\n"
             "module child(interface port_a, interface port_b);\n"
             "endmodule\n"
             "module top;\n"
             "  axi_if a_inst();\n"
             "  apb_if b_inst();\n"
             "  child u(.port_a(a_inst), .port_b(b_inst));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     MultipleInterfacePortsOneUnconnectedErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface axi_if;\n"
      "  logic [31:0] addr;\n"
      "endinterface\n"
      "interface apb_if;\n"
      "  logic [15:0] paddr;\n"
      "endinterface\n"
      "module child(interface port_a, interface port_b);\n"
      "endmodule\n"
      "module top;\n"
      "  axi_if a_inst();\n"
      "  child u(.port_a(a_inst));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfacePortConnectionRulesElaboration,
     InterfacePortWithNonInterfaceMixedPorts) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(interface port_a, input logic clk, output logic q);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  logic clk, q;\n"
             "  child u(.port_a(inst), .clk(clk), .q(q));\n"
             "endmodule\n"));
}

TEST(InterfacePortConnectionRulesElaboration,
     NamedInterfacePortConnectedViaPositional) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "endinterface\n"
             "module child(bus_if port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(inst);\n"
             "endmodule\n"));
}

}  // namespace
