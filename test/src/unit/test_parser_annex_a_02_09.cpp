#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

// modport_simple_port's dotted form makes the connecting expression optional:
// `. port_identifier ( [ expression ] )`. Exercise the empty-parentheses branch
// where no expression is supplied, leaving the recorded expr null.
TEST(ModportDeclarationParsing, DotNotationEmptyExpression) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(.data());\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "data");
  EXPECT_EQ(mp->ports[0].expr, nullptr);
}

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

// modport_tf_port's method_prototype alternative also covers the function form
// (the task form is exercised above). This reaches the function-prototype branch
// of the tf-port parser, recording an imported method prototype on the port.
TEST(ModportDeclarationParsing, ImportFunctionMethodPrototype) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import function bit Read(input int addr));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_NE(mp->ports[0].prototype, nullptr);
}

TEST(ModportDeclarationParsing, AttrOnSimplePorts) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  logic a;\n"
              "  modport target((* synthesis *) input a);\n"
              "endinterface\n"));
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

}
