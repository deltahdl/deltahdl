

#include "fixture_elaborator.h"

namespace {

TEST(InterfaceModport, InterfaceWithModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceModport, MultipleModportsElaborate) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "  modport slave(input data);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceModport, ModuleWithNamedInterfacePortAndModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "endinterface\n"
             "module m(bus.master b);\n"
             "endmodule\n"));
}

TEST(InterfaceModport, ModuleWithGenericInterfacePortAndModportElaborates) {
  EXPECT_TRUE(
      ElabOk("module m(interface.master b);\n"
             "endmodule\n"));
}

// §25.5: a modport whose simple items name signals the interface declares is
// legal — the elaborator accepts it.
TEST(InterfaceModportNames, ModportNamesMayBeDeclaredSignals) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic req, gnt;\n"
             "  modport master(input req, output gnt);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

// §25.5: a modport may not implicitly declare a new port, so naming something
// the interface never declares is an elaboration error.
TEST(InterfaceModportNames, ModportNameNotDeclaredByInterfaceErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic data;\n"
      "  modport master(output missing);\n"
      "endinterface\n"
      "module top;\n"
      "  bus i();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §25.5: a name the interface contributes through its own port list (e.g. clk)
// counts as declared by that interface and may appear in a modport.
TEST(InterfaceModportNames, ModportNameMayBeAnInterfacePort) {
  EXPECT_TRUE(
      ElabOk("interface bus(input logic clk);\n"
             "  logic data;\n"
             "  modport master(input clk, output data);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

// §25.5: every declarator of a comma-separated signal declaration is a distinct
// name the interface declares, so each may be referenced by a modport.
TEST(InterfaceModportNames, ModportNamesFromCommaDeclarationResolve) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic a, b;\n"
             "  modport master(input a, output b);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

// §25.5: when the module header and the instance connection both select a
// modport, choosing the same one is legal.
TEST(InterfaceModportAgreement,
     HeaderAndConnectionSelectSameModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "  modport master(output data);\n"
             "  modport slave(input data);\n"
             "endinterface\n"
             "module child(bus_if.slave port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(.port_a(inst.slave));\n"
             "endmodule\n"));
}

// §25.5: when both sites select a modport, they shall name the same one;
// selecting different modports is an elaboration error.
TEST(InterfaceModportAgreement,
     HeaderAndConnectionSelectDifferentModportsErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_if;\n"
      "  logic data;\n"
      "  modport master(output data);\n"
      "  modport slave(input data);\n"
      "endinterface\n"
      "module child(bus_if.master port_a);\n"
      "endmodule\n"
      "module top;\n"
      "  bus_if inst();\n"
      "  child u(.port_a(inst.slave));\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §25.5: selecting a modport in the header alone leaves nothing to disagree
// with, so a bare instance connection is accepted.
TEST(InterfaceModportAgreement, ModportSelectedOnlyInHeaderElaborates) {
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

// §25.5: with no modport selected in the header or the connection, an interface
// port's nets and variables stay accessible — here a member is both read and
// driven through a modport-less port and the elaborator raises no error.
TEST(InterfaceDefaultAccess, ModportlessInterfacePortPermitsMemberAccess) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "  logic avail;\n"
      "  always @(posedge a.clk) a.gnt <= a.req & avail;\n"
      "endmodule\n",
      f, "memMod");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
