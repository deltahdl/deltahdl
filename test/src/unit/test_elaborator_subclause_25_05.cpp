

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

// §25.5: a modport restricts which interface signals a module may reach. A
// module reaching a member the selected modport lists is accepted — the
// restriction admits the listed signal.
TEST(InterfaceModportAccess, ListedMemberIsAccessibleThroughModport) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic ctrl, status;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  always @(*) x = b.status;\n"
      "endmodule\n",
      f, "child");
  EXPECT_FALSE(f.has_errors);
}

// §25.5: the same restriction rejects a member the selected modport omits —
// reaching a signal outside the modport list through the modport port is an
// elaboration error, which is the whole point of restricting access.
TEST(InterfaceModportAccess, UnlistedMemberIsInaccessibleThroughModport) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic ctrl, status, secret;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  always @(*) x = b.secret;\n"
      "endmodule\n",
      f, "child");
  EXPECT_TRUE(f.has_errors);
}

// §25.5 input form: the access restriction applies to NET members too (the
// LRM's own modport example lists `wire` signals). A net the modport lists is
// reachable through the modport port.
TEST(InterfaceModportAccess, ListedNetMemberIsAccessibleThroughModport) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  wire ctrl, status;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  always @(*) x = b.status;\n"
      "endmodule\n",
      f, "child");
  EXPECT_FALSE(f.has_errors);
}

// §25.5 negative, net input form: a net member the modport omits is just as
// inaccessible through the modport port as an omitted variable member.
TEST(InterfaceModportAccess, UnlistedNetMemberIsInaccessibleThroughModport) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  wire ctrl, status, secret;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  always @(*) x = b.secret;\n"
      "endmodule\n",
      f, "child");
  EXPECT_TRUE(f.has_errors);
}

// §25.5: a modport list name may be selected in the port connection alone, with
// the module header declaring a plain interface port — the elaborator accepts
// the connection-side modport selection.
TEST(InterfaceModportAgreement,
     ConnectionSelectsModportWithPlainHeaderElaborates) {
  EXPECT_TRUE(
      ElabOk("interface bus_if;\n"
             "  logic data;\n"
             "  modport slave(input data);\n"
             "endinterface\n"
             "module child(bus_if port_a);\n"
             "endmodule\n"
             "module top;\n"
             "  bus_if inst();\n"
             "  child u(.port_a(inst.slave));\n"
             "endmodule\n"));
}

// §25.5 input form: the default-access rule covers NET members as well. With no
// modport selected, a net member of an interface port is accessible (inout),
// so reading it raises no error.
TEST(InterfaceDefaultAccess, ModportlessInterfacePortPermitsNetMemberAccess) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  wire ctrl, status;\n"
      "endinterface\n"
      "module child(bus b);\n"
      "  logic x;\n"
      "  always @(*) x = b.status;\n"
      "endmodule\n",
      f, "child");
  EXPECT_FALSE(f.has_errors);
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
