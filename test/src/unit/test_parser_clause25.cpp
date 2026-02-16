#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// --- End label on endinterface (LRM §25) ---

TEST(ParserSection25, EndinterfaceLabel) {
  auto r = Parse(
      "interface simple_bus;\n"
      "endinterface : simple_bus\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
}

TEST(ParserSection25, EndinterfaceNoLabel) {
  auto r = Parse(
      "interface my_if;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "my_if");
}

// --- Modport with port expressions (LRM §25.5.4) ---

TEST(ParserSection25, ModportPortExpressionName) {
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

TEST(ParserSection25, ModportPortExpressionPort) {
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

TEST(ParserSection25, ModportPortExpressionPartSelect) {
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

TEST(ParserSection25, ModportMixedDirectionAndExprFirst) {
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

TEST(ParserSection25, ModportMixedDirectionAndExprSecond) {
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

// --- Modport import/export (LRM §25.5, §25.7) ---

TEST(ParserSection25, ModportImportExportName) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "target");
  ASSERT_EQ(mp->ports.size(), 2);
}

static void VerifyImportExportPort(const ModportPort& port, bool is_import,
                                   bool is_export, const char* name) {
  EXPECT_EQ(port.is_import, is_import);
  EXPECT_EQ(port.is_export, is_export);
  EXPECT_EQ(port.name, name);
}

TEST(ParserSection25, ModportImportExportPorts) {
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

TEST(ParserSection25, ModportImportWithDirectionFirst) {
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

TEST(ParserSection25, ModportImportWithDirectionSecond) {
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

// --- Virtual interface (LRM §25.9) ---

TEST(ParserSection25, VirtualInterfaceDecl) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->name, "bus_if");
}

TEST(ParserSection25, VirtualInterfaceNoKeyword) {
  auto r = Parse(
      "module top;\n"
      "  virtual simple_bus bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->name, "bus_if");
}

TEST(ParserSection25, VirtualInterfaceWithModportKind) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus.target bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->name, "bus_if");
}

TEST(ParserSection25, VirtualInterfaceWithModportNames) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus.target bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->data_type.modport_name, "target");
}

// --- Multiple modport items per statement (LRM §25.5) ---

static void VerifyModportItem(const ModportDecl* mp, const char* mp_name,
                              Direction dir, const char* port_name) {
  EXPECT_EQ(mp->name, mp_name);
  ASSERT_EQ(mp->ports.size(), 1);
  EXPECT_EQ(mp->ports[0].direction, dir);
  EXPECT_EQ(mp->ports[0].name, port_name);
}

TEST(ParserSection25, MultipleModportItems) {
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

TEST(ParserSection25, MultipleModportThreeItems) {
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

// --- Virtual interface with parameter (LRM §25.9) ---

TEST(ParserSection25, VirtualInterfaceAssignment) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus vif;\n"
      "  initial begin\n"
      "    vif = null;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kVirtualInterface);
}

TEST(ParserSection25, VirtualInterfaceMultipleDecls) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface bus_if a_if;\n"
      "  virtual bus_if b_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(mod->items[0]->name, "a_if");
  EXPECT_EQ(mod->items[1]->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(mod->items[1]->name, "b_if");
}
