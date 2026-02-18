#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// §A.2.9 modport_declaration ::= modport modport_item { , modport_item } ;

TEST(ParserA29, BasicModportDecl) {
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

// modport_item ::= modport_identifier ( modport_ports_declaration { , ... } )

TEST(ParserA29, MultipleModportItems) {
  auto r = Parse(
      "interface bus;\n"
      "  logic a, b;\n"
      "  modport init(output a), tgt(input b);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 2u);
  EXPECT_EQ(iface->modports[0]->name, "init");
  EXPECT_EQ(iface->modports[1]->name, "tgt");
}

// modport_simple_ports_declaration ::=
//   port_direction modport_simple_port { , modport_simple_port }

TEST(ParserA29, MultipleSimplePortsSameDir) {
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

TEST(ParserA29, AllFourDirections) {
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

// modport_simple_port ::= . port_identifier ( [ expression ] )

TEST(ParserA29, PortExprDotNotation) {
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

TEST(ParserA29, PortExprEmpty) {
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

TEST(ParserA29, PortExprMixedWithSimple) {
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

// modport_clocking_declaration ::= clocking clocking_identifier

TEST(ParserA29, ClockingInModport) {
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

TEST(ParserA29, ClockingMixedWithDirectionPorts) {
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

// modport_tf_ports_declaration ::=
//   import_export modport_tf_port { , modport_tf_port }

TEST(ParserA29, ImportSingleIdentifier) {
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

TEST(ParserA29, ImportMultipleIdentifiers) {
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

TEST(ParserA29, ExportSingleIdentifier) {
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

TEST(ParserA29, ExportMultipleIdentifiers) {
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

// modport_tf_port ::= method_prototype (task prototype)

TEST(ParserA29, ImportTaskPrototype) {
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

TEST(ParserA29, ImportFunctionPrototype) {
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

TEST(ParserA29, ImportMultiplePrototypes) {
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

TEST(ParserA29, ExportTaskPrototype) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport target(export task Read(input logic [7:0] addr));\n"
              "endinterface\n"));
}

TEST(ParserA29, ImportTaskNoArgs) {
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

TEST(ParserA29, ImportFunctionVoidReturn) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport init(import function void reset());\n"
              "endinterface\n"));
}

// Mixed modport_ports_declarations

TEST(ParserA29, MixedDirImportExport) {
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

TEST(ParserA29, MixedDirImportClocking) {
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

TEST(ParserA29, ImportThenDirectionPorts) {
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

// attribute_instance on modport_ports_declaration

TEST(ParserA29, AttrOnSimplePorts) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  logic a;\n"
              "  modport target((* synthesis *) input a);\n"
              "endinterface\n"));
}

TEST(ParserA29, AttrOnImportPort) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport target((* synthesis *) import Read);\n"
              "endinterface\n"));
}

TEST(ParserA29, AttrOnClockingPort) {
  EXPECT_TRUE(
      ParseOk("interface bus(input logic clk);\n"
              "  clocking sb @(posedge clk);\n"
              "  endclocking\n"
              "  modport target((* synthesis *) clocking sb);\n"
              "endinterface\n"));
}

// Direction persists across simple ports (§25.5)

TEST(ParserA29, DirectionPersistsAcrossPorts) {
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

// Complex integration: all production alternatives together

TEST(ParserA29, AllAlternativesTogether) {
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

TEST(ParserA29, FullPrototypeMixed) {
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

}  // namespace
