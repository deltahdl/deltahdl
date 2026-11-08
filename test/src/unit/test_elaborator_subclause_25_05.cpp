#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "modport 'master' references 'missing', which "
                            "interface 'bus' does not declare",
                            3, "25.5"));
}

TEST(InterfaceModportNames, ModportNameMayBeAnInterfacePort) {
  EXPECT_TRUE(
      ElabOk("interface bus(input logic clk);\n"
             "  logic data;\n"
             "  modport master(input clk, output data);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceModportNames, ModportNamesFromCommaDeclarationResolve) {
  EXPECT_TRUE(
      ElabOk("interface bus;\n"
             "  logic a, b;\n"
             "  modport master(input a, output b);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "interface port 'port_a' selects modport 'master' in the module header "
      "but 'slave' in the instance connection; both shall name the same "
      "modport",
      10, "25.5"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master' of interface 'bus'",
      7, "25.5"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master' of interface 'bus'",
      7, "25.5"));
}

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

TEST(InterfaceModportAccess, UnlistedMemberNames25_5) {
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master'", 7, "25.5"));
}

TEST(InterfaceModportNames, UndeclaredModportNameNames25_5) {
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "which interface 'bus'", 3, "25.5"));
}

TEST(InterfaceModportAccess, UnlistedMemberInForkArmIsInaccessible) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic ctrl, status, secret;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  initial fork\n"
      "    x = b.secret;\n"
      "  join\n"
      "endmodule\n",
      f, "child");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master' of interface 'bus'",
      8, "25.5"));
}

TEST(InterfaceModportAccess, UnlistedMemberInForInitializationIsInaccessible) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic ctrl, status, secret;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial for (x = b.secret; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f, "child");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master' of interface 'bus'",
      8, "25.5"));
}

TEST(InterfaceModportAccess, UnlistedMemberInForStepIsInaccessible) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic ctrl, status, secret;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; x = b.secret) ;\n"
      "endmodule\n",
      f, "child");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master' of interface 'bus'",
      8, "25.5"));
}

TEST(InterfaceModportAccess, UnlistedMemberInAssertionPassStmtIsInaccessible) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic ctrl, status, secret;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  initial assert (1) x = b.secret;\n"
      "endmodule\n",
      f, "child");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master' of interface 'bus'",
      7, "25.5"));
}

TEST(InterfaceModportAccess, UnlistedMemberInAssertionFailStmtIsInaccessible) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic ctrl, status, secret;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  initial assert (1) else x = b.secret;\n"
      "endmodule\n",
      f, "child");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master' of interface 'bus'",
      7, "25.5"));
}

TEST(InterfaceModportAccess, UnlistedMemberInRandcaseItemIsInaccessible) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic ctrl, status, secret;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  initial randcase\n"
      "    1 : x = b.secret;\n"
      "  endcase\n"
      "endmodule\n",
      f, "child");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master' of interface 'bus'",
      8, "25.5"));
}

TEST(InterfaceModportAccess,
     UnlistedMemberInRandsequenceCodeBlockIsInaccessible) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus;\n"
      "  logic ctrl, status, secret;\n"
      "  modport master(input status, output ctrl);\n"
      "endinterface\n"
      "module child(bus.master b);\n"
      "  logic x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = b.secret; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "child");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'secret' is not accessible through modport 'master' of interface 'bus'",
      9, "25.5"));
}

TEST(InterfaceModport, NestedInterfaceModportNamingOuterSignalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "interface i;\n"
      "  wire x, y;\n"
      "  interface illegal_i;\n"
      "    wire a, b, c, d;\n"
      "    modport initiator(input a, b, x, output c, d, y);\n"
      "  endinterface : illegal_i\n"
      "  illegal_i ii();\n"
      "endinterface : i\n"
      "module top;\n"
      "  i u();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "modport 'initiator' references 'x', which "
                            "interface 'illegal_i' does not declare",
                            5, "25.5"));
}

TEST(InterfaceModportNames, AnElaboratedInterfaceCarriesItsModports) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface ifc;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "  modport mq(input b);\n"
      "endinterface\n"
      "module top;\n"
      "  ifc i0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  const delta::RtlirModule* ifc = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(ifc, nullptr);
  ASSERT_EQ(ifc->modports.size(), 2u);
  EXPECT_EQ(ifc->modports[0]->name, "mp");
  EXPECT_EQ(ifc->modports[0]->ports.size(), 2u);
  EXPECT_EQ(ifc->modports[1]->name, "mq");
}

TEST(InterfaceModportNames, AnElaboratedModuleCarriesNoModports) {
  ElabFixture f;
  auto* design = Elaborate("module top;\nendmodule\n", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(design->top_modules[0]->modports.empty());
}

TEST(ModportElaboration, AssigningAModportInputVariableIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface i2; logic [3:0] a; logic c; modport initiator(input a, "
      "output c); endinterface\n"
      "module m(i2.initiator i);\n"
      "  initial begin i.a = 1; i.c = 1; end\n"
      "  assign i.a[0] = 1;\n"
      "endmodule\n"
      "module top; i2 i(); m u1(.i(i)); endmodule\n",
      f, "top");
  for (int line : {3, 4}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'a' is an input of modport 'initiator' of "
                              "interface 'i2' and cannot be the target of an "
                              "assignment",
                              line, "25.5"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'c' is an input of modport 'initiator' of "
                             "interface 'i2' and cannot be the target of an "
                             "assignment",
                             3, "25.5"));
}

TEST(ModportElaboration, AssigningAModportInputNetIsNotRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface i4; wire w; modport mp(input w); endinterface\n"
      "module m(i4.mp i); assign i.w = 1; endmodule\n"
      "module top; i4 i(); m u1(.i(i)); endmodule\n",
      f, "top");
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'w' is an input of modport 'mp' of interface "
                             "'i4' and cannot be the target of an assignment",
                             2, "25.5"));
}

}  // namespace
