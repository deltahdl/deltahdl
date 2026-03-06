#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §A.2.9 modport_declaration ::= modport modport_item { , modport_item } ;

TEST(ParserA29, ModportSingleItem) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic clk, data;\n"
      "  modport master(input clk, output data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
}

TEST(ParserA29, ModportMultipleItems) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic clk, data;\n"
      "  modport master(input clk, output data),\n"
      "          slave(input clk, input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
  EXPECT_EQ(r.cu->interfaces[0]->modports[1]->name, "slave");
}

// §A.2.9 modport_simple_ports_declaration

TEST(ParserA29, ModportSimplePortsInput) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a, b;\n"
      "  modport mp(input a, b);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 2u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[0].name, "a");
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].name, "b");
}

TEST(ParserA29, ModportSimplePortsOutput) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic q;\n"
      "  modport mp(output q);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kOutput);
}

TEST(ParserA29, ModportSimplePortsInout) {
  auto r = Parse(
      "interface ifc;\n"
      "  wire bus;\n"
      "  modport mp(inout bus);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInout);
}

TEST(ParserA29, ModportSimplePortsRef) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic sig;\n"
      "  modport mp(ref sig);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kRef);
}

// §A.2.9 modport_simple_port ::= . port_identifier ( [ expression ] )

TEST(ParserA29, ModportSimplePortExplicitExpr) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a;\n"
      "  modport mp(input .x(a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "x");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ParserA29, ModportSimplePortEmptyExpr) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a;\n"
      "  modport mp(input .x());\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "x");
  EXPECT_EQ(mp->ports[0].expr, nullptr);
}

// §A.2.9 modport_tf_ports_declaration (import/export)

TEST(ParserA29, ModportTfPortsImportIdentifier) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(import my_func);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  VerifyImportExportPort(mp->ports[0], true, false, "my_func");
}

TEST(ParserA29, ModportTfPortsExportIdentifier) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(export my_task);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  VerifyImportExportPort(mp->ports[0], false, true, "my_task");
}

// §A.2.9 modport_tf_port ::= method_prototype

TEST(ParserA29, ModportImportFunctionPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(import function int compute(int a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mp->ports[0].prototype->name, "compute");
}

TEST(ParserA29, ModportImportTaskPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(import task do_work(int x));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kTaskDecl);
}

// §A.2.9 modport_clocking_declaration ::= clocking clocking_identifier

TEST(ParserA29, ModportClockingDecl) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic clk;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  modport mp(clocking cb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_EQ(mp->ports[0].name, "cb");
}

// Mixed port directions in a modport

TEST(ParserA29, ModportMixedDirections) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic clk, data_in, data_out, valid;\n"
      "  modport master(input clk, valid, output data_out, inout data_in);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 4u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[0].name, "clk");
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].name, "valid");
  EXPECT_EQ(mp->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(mp->ports[2].name, "data_out");
  EXPECT_EQ(mp->ports[3].direction, Direction::kInout);
  EXPECT_EQ(mp->ports[3].name, "data_in");
}

// Multiple modport declarations in one interface

TEST(ParserA29, MultipleModportDecls) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a, b;\n"
      "  modport mp1(input a);\n"
      "  modport mp2(output b);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "mp1");
  EXPECT_EQ(r.cu->interfaces[0]->modports[1]->name, "mp2");
}

}  // namespace
