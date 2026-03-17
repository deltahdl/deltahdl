#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- modport_declaration ---

TEST(ModportDeclarationParsing, ModportSingleItem) {
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

TEST(ModportDeclarationParsing, ModportMultipleItems) {
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

TEST(ModportDeclarationParsing, MultipleModportDecls) {
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

TEST(ModportDeclarationParsing, SingleInputPort) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a;\n"
      "  modport target(input a);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "target");
}

TEST(ModportDeclarationParsing, MultipleModportItems) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a;\n"
      "  logic b;\n"
      "  modport m1(input a), m2(output b);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 2);
  VerifyModportItem(iface->modports[0], "m1", Direction::kInput, "a");
  VerifyModportItem(iface->modports[1], "m2", Direction::kOutput, "b");
}

TEST(ModportDeclarationParsing, MultipleModportThreeItems) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a;\n"
      "  logic b;\n"
      "  logic c;\n"
      "  modport m1(input a), m2(output b), m3(inout c);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 3);
  const std::string kExpectedNames[] = {"m1", "m2", "m3"};
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(iface->modports[i]->name, kExpectedNames[i]);
  }
  EXPECT_EQ(iface->modports[2]->ports[0].direction, Direction::kInout);
}

struct ModportPortExpected {
  Direction dir;
  const char* name;
};

static void VerifyModportPorts(const std::vector<ModportPort>& ports,
                               const ModportPortExpected expected[],
                               size_t count) {
  ASSERT_EQ(ports.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(ports[i].direction, expected[i].dir) << "port " << i;
    EXPECT_EQ(ports[i].name, expected[i].name) << "port " << i;
  }
}

TEST(ModportDeclarationParsing, SingleOutputPortVerified) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] data;\n"
      "  modport master(output data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "master");
  ModportPortExpected expected[] = {{Direction::kOutput, "data"}};
  VerifyModportPorts(mp->ports, expected, std::size(expected));
}

TEST(ModportDeclarationParsing, TwoInputPortsSameDirection) {
  auto r = Parse(
      "interface bus;\n"
      "  logic addr;\n"
      "  logic data;\n"
      "  modport slave(input addr, input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "slave");
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
}

TEST(ModportDeclarationParsing, TwoModportsMultiplePorts) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic [7:0] data;\n"
      "  logic valid, ready;\n"
      "  modport master (output data, output valid, input ready);\n"
      "  modport slave (input data, input valid, output ready);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  EXPECT_EQ(ifc->name, "bus_if");
  ASSERT_EQ(ifc->modports.size(), 2u);
  EXPECT_EQ(ifc->modports[0]->name, "master");
  EXPECT_EQ(ifc->modports[1]->name, "slave");
}

TEST(ModportDeclarationParsing, TwoModportsDeclCount) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic [7:0] data;\n"
      "  modport master(output data);\n"
      "  modport slave(input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "bus_if");
  EXPECT_EQ(r.cu->interfaces[0]->modports.size(), 2u);
}

TEST(ModportDeclarationParsing, ModportDeclHasSourceLoc) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a;\n"
      "  modport target(input a);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_TRUE(mp->loc.IsValid());
}

TEST(ModportDeclarationParsing, MasterSlaveDirections) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  modport master(output req, input gnt);\n"
      "  modport slave(input req, output gnt);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
  EXPECT_EQ(r.cu->interfaces[0]->modports[1]->name, "slave");
}

// --- modport_simple_ports_declaration ---

TEST(ModportDeclarationParsing, ModportSimplePortsInput) {
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

TEST(ModportDeclarationParsing, ModportSimplePortsOutput) {
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

TEST(ModportDeclarationParsing, ModportSimplePortsInout) {
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

TEST(ModportDeclarationParsing, ModportSimplePortsRef) {
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

TEST(ModportDeclarationParsing, MultipleSimplePortsSameDir) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a, b, c;\n"
      "  modport target(input a, b, c);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 3u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[0].name, "a");
  EXPECT_EQ(mp->ports[1].name, "b");
  EXPECT_EQ(mp->ports[2].name, "c");
}

TEST(ModportDeclarationParsing, DirectionPersistsAcrossPorts) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a, b, c, d;\n"
      "  modport target(input a, b, output c, d);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 4u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(mp->ports[3].direction, Direction::kOutput);
}

TEST(ModportDeclarationParsing, AllFourDirections) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a, b, c;\n"
      "  wire d;\n"
      "  modport mp(input a, output b, inout c, ref d);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 4u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kInout);
  EXPECT_EQ(mp->ports[3].direction, Direction::kRef);
}

TEST(ModportDeclarationParsing, InputAndOutputMixed) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a, b, c;\n"
      "  modport mp(input a, b, output c);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 3u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kOutput);
}

// --- modport_simple_port ---

TEST(ModportDeclarationParsing, ModportSimplePortExplicitExpr) {
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

TEST(ModportDeclarationParsing, ModportSimplePortEmptyExpr) {
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

TEST(ModportDeclarationParsing, PortExprDotNotation) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] r;\n"
      "  modport A(output .P(r[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ModportDeclarationParsing, PortExprEmpty) {
  auto r = Parse(
      "interface bus;\n"
      "  modport A(input .P());\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_EQ(mp->ports[0].expr, nullptr);
}

TEST(ModportDeclarationParsing, PortExprMixedWithSimple) {
  auto r = Parse(
      "interface I;\n"
      "  logic [7:0] r;\n"
      "  bit R;\n"
      "  modport A(output .P(r[3:0]), R);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
  EXPECT_EQ(mp->ports[1].name, "R");
}

TEST(ModportDeclarationParsing, DotNotationModportName) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  modport target(.data(bus_data));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 1);
  auto* mp = iface->modports[0];
  EXPECT_EQ(mp->name, "target");
}

TEST(ModportDeclarationParsing, DotNotationPortNameAndExpr) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  modport target(.data(bus_data));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1);
  EXPECT_EQ(mp->ports[0].name, "data");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ModportDeclarationParsing, ModportPortExpressionPartSelect) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  modport target(.data(bus_data[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1);
  EXPECT_EQ(mp->ports[0].name, "data");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

// --- modport_ports_declaration (mixed alternatives, attributes) ---

TEST(ModportDeclarationParsing, ModportMixedDirections) {
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

TEST(ModportDeclarationParsing, ModportImportWithDirectionFirst) {
  auto r = Parse(
      "interface bus;\n"
      "  logic data;\n"
      "  modport target(input data, import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[0].name, "data");
  EXPECT_FALSE(mp->ports[0].is_import);
}

TEST(ModportDeclarationParsing, DirectionPortBeforeDotNotation) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  logic clk;\n"
      "  modport target(input clk, .data(bus_data[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[0].name, "clk");
  EXPECT_EQ(mp->ports[0].expr, nullptr);
}

TEST(ModportDeclarationParsing, DotNotationAfterDirectionPort) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  logic clk;\n"
      "  modport target(input clk, .data(bus_data[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[1].name, "data");
  EXPECT_NE(mp->ports[1].expr, nullptr);
}

TEST(ModportDeclarationParsing, MixedDirImportExport) {
  auto r = Parse(
      "interface bus;\n"
      "  logic req, gnt;\n"
      "  modport target(\n"
      "    input req,\n"
      "    output gnt,\n"
      "    import Read,\n"
      "    export Write\n"
      "  );\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 4u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kOutput);
  EXPECT_TRUE(mp->ports[2].is_import);
  EXPECT_TRUE(mp->ports[3].is_export);
}

TEST(ModportDeclarationParsing, ModportImportWithDirectionSecond) {
  auto r = Parse(
      "interface bus;\n"
      "  logic data;\n"
      "  modport target(input data, import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_FALSE(mp->ports[0].is_export);
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].name, "Read");
}

TEST(ModportDeclarationParsing, ImportThenDirectionPorts) {
  auto r = Parse(
      "interface bus;\n"
      "  logic data;\n"
      "  modport target(import Read, input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].name, "data");
}

TEST(ModportDeclarationParsing, AllPortKindsMixed) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  logic req, gnt;\n"
              "  logic [7:0] addr, data;\n"
              "  modport init(\n"
              "    input gnt,\n"
              "    output req, addr,\n"
              "    ref data,\n"
              "    import task Read(input logic [7:0] raddr),\n"
              "           task Write(input logic [7:0] waddr)\n"
              "  );\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, AttrOnSimplePorts) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  logic a;\n"
              "  modport target((* synthesis *) input a);\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, AttrOnImportPort) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport target((* synthesis *) import Read);\n"
              "endinterface\n"));
}

// --- modport_tf_ports_declaration / modport_tf_port / import_export ---

TEST(ModportDeclarationParsing, ModportTfPortsImportIdentifier) {
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

TEST(ModportDeclarationParsing, ModportTfPortsExportIdentifier) {
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

TEST(ModportDeclarationParsing, ImportMultipleIdentifiers) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].name, "Write");
}

TEST(ModportDeclarationParsing, ImportSingleIdentifier) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
}

TEST(ModportDeclarationParsing, ImportExportModportName) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "target");
  ASSERT_EQ(mp->ports.size(), 2);
}

TEST(ModportDeclarationParsing, ImportExportPortsVerified) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  VerifyImportExportPort(mp->ports[0], true, false, "Read");
  VerifyImportExportPort(mp->ports[1], false, true, "Write");
}

TEST(ModportDeclarationParsing, ImportFlagNotExport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_FALSE(mp->ports[0].is_export);
}

TEST(ModportDeclarationParsing, ExportSingleIdentifier) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_export);
  EXPECT_EQ(mp->ports[0].name, "Write");
}

TEST(ModportDeclarationParsing, ExportMultipleIdentifiers) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(export Read, Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_export);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_TRUE(mp->ports[1].is_export);
  EXPECT_EQ(mp->ports[1].name, "Write");
}

TEST(ModportDeclarationParsing, ExportFlagNotImport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_FALSE(mp->ports[0].is_import);
  EXPECT_TRUE(mp->ports[0].is_export);
}

// --- modport_tf_port with method_prototype ---

TEST(ModportDeclarationParsing, ModportImportFunctionPrototype) {
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

TEST(ModportDeclarationParsing, ModportImportTaskPrototype) {
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

TEST(ModportDeclarationParsing, ImportFunctionPrototype) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import function int compute(input int a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mp->ports[0].prototype->name, "compute");
}

TEST(ModportDeclarationParsing, ImportTaskNoArgs) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import task doWork);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->name, "doWork");
}

TEST(ModportDeclarationParsing, ImportFunctionVoidReturn) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport init(import function void reset());\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, FunctionPrototypeReturnType) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import function int compute(input int a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mp->ports[0].prototype->data_type.kind, DataTypeKind::kInt);
}

TEST(ModportDeclarationParsing, TaskPrototypeHasArgs) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import task Read(input logic [7:0] raddr));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_FALSE(mp->ports[0].prototype->func_args.empty());
}

TEST(ModportDeclarationParsing, ImportTaskPrototype) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import task Read(input logic [7:0] raddr));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(mp->ports[0].prototype->name, "Read");
}

TEST(ModportDeclarationParsing, ExportTaskPrototype) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport target(export task Read(input logic [7:0] addr));\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, ImportMultiplePrototypes) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(\n"
      "    import task Read(input logic [7:0] raddr),\n"
      "           task Write(input logic [7:0] waddr)\n"
      "  );\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].prototype->name, "Read");
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].prototype->name, "Write");
}

// --- modport_clocking_declaration ---

TEST(ModportDeclarationParsing, ModportClockingDecl) {
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

TEST(ModportDeclarationParsing, ClockingInModport) {
  auto r = Parse(
      "interface A_Bus(input logic clk);\n"
      "  clocking sb @(posedge clk);\n"
      "  endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_EQ(mp->ports[0].name, "sb");
}

TEST(ModportDeclarationParsing, ClockingMixedWithDirectionPorts) {
  auto r = Parse(
      "interface A_Bus(input logic clk);\n"
      "  wire req, gnt;\n"
      "  clocking sb @(posedge clk);\n"
      "  endclocking\n"
      "  modport DUT(input clk, req, output gnt);\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 2u);
  EXPECT_EQ(iface->modports[0]->name, "DUT");
  EXPECT_EQ(iface->modports[1]->name, "STB");
  EXPECT_TRUE(iface->modports[1]->ports[0].is_clocking);
}

TEST(ModportDeclarationParsing, MixedDirImportClocking) {
  EXPECT_TRUE(
      ParseOk("interface A_Bus(input logic clk);\n"
              "  wire req, gnt;\n"
              "  clocking sb @(posedge clk);\n"
              "  endclocking\n"
              "  modport STB(\n"
              "    input req,\n"
              "    output gnt,\n"
              "    import Read,\n"
              "    clocking sb\n"
              "  );\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, AttrOnClockingPort) {
  EXPECT_TRUE(
      ParseOk("interface bus(input logic clk);\n"
              "  clocking sb @(posedge clk);\n"
              "  endclocking\n"
              "  modport target((* synthesis *) clocking sb);\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, AllAlternativesTogether) {
  EXPECT_TRUE(
      ParseOk("interface complex_bus(input logic clk);\n"
              "  logic req, gnt;\n"
              "  logic [7:0] addr, data;\n"
              "  clocking sb @(posedge clk);\n"
              "    input gnt;\n"
              "    output req, addr;\n"
              "  endclocking\n"
              "  modport DUT(\n"
              "    input clk, req, addr,\n"
              "    output gnt,\n"
              "    ref data\n"
              "  );\n"
              "  modport STB(clocking sb);\n"
              "  modport TB(\n"
              "    input gnt,\n"
              "    output req, addr,\n"
              "    import Read, Write\n"
              "  );\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, ClockingPortNotImportExport) {
  auto r = Parse(
      "interface A_Bus(input logic clk);\n"
      "  clocking sb @(posedge clk);\n"
      "  endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_FALSE(mp->ports[0].is_import);
  EXPECT_FALSE(mp->ports[0].is_export);
  EXPECT_EQ(mp->ports[0].direction, Direction::kNone);
}

// --- Error conditions ---

TEST(ModportDeclarationParsing, MissingModportName) {
  EXPECT_FALSE(
      ParseOk("interface ifc;\n"
              "  modport (input a);\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, MissingOpenParen) {
  EXPECT_FALSE(
      ParseOk("interface ifc;\n"
              "  logic a;\n"
              "  modport mp input a);\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, MissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("interface ifc;\n"
              "  logic a;\n"
              "  modport mp(input a;\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, MissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("interface ifc;\n"
              "  logic a;\n"
              "  modport mp(input a)\n"
              "endinterface\n"));
}

// --- Edge cases ---

TEST(ModportDeclarationParsing, ExportFunctionPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(export function void compute(int a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_export);
  EXPECT_FALSE(mp->ports[0].is_import);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mp->ports[0].prototype->name, "compute");
}

TEST(ModportDeclarationParsing, MultipleClockingPorts) {
  auto r = Parse(
      "interface ifc(input logic clk1, input logic clk2);\n"
      "  clocking cb1 @(posedge clk1); endclocking\n"
      "  clocking cb2 @(posedge clk2); endclocking\n"
      "  modport mp(clocking cb1, clocking cb2);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_EQ(mp->ports[0].name, "cb1");
  EXPECT_TRUE(mp->ports[1].is_clocking);
  EXPECT_EQ(mp->ports[1].name, "cb2");
}

TEST(ModportDeclarationParsing, AttrOnExportPort) {
  EXPECT_TRUE(
      ParseOk("interface ifc;\n"
              "  modport mp((* synthesis *) export Write);\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, DotNotationWithoutDirection) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a;\n"
      "  modport mp(.x(a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "x");
  EXPECT_NE(mp->ports[0].expr, nullptr);
  EXPECT_EQ(mp->ports[0].direction, Direction::kNone);
}

}  // namespace
