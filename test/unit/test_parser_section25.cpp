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

TEST(ParserSection25, ModportPortExpression) {
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

TEST(ParserSection25, ModportMixedDirectionAndExpr) {
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
  EXPECT_EQ(mp->ports[1].name, "data");
  EXPECT_NE(mp->ports[1].expr, nullptr);
}

// --- Modport import/export (LRM §25.5, §25.7) ---

TEST(ParserSection25, ModportImportExport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "target");
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_TRUE(mp->ports[1].is_export);
  EXPECT_EQ(mp->ports[1].name, "Write");
}

TEST(ParserSection25, ModportImportWithDirection) {
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

TEST(ParserSection25, VirtualInterfaceWithModport) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus.target bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->data_type.modport_name, "target");
  EXPECT_EQ(item->name, "bus_if");
}

// --- Multiple modport items per statement (LRM §25.5) ---

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
  EXPECT_EQ(iface->modports[0]->name, "m1");
  ASSERT_EQ(iface->modports[0]->ports.size(), 1);
  EXPECT_EQ(iface->modports[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(iface->modports[0]->ports[0].name, "a");
  EXPECT_EQ(iface->modports[1]->name, "m2");
  ASSERT_EQ(iface->modports[1]->ports.size(), 1);
  EXPECT_EQ(iface->modports[1]->ports[0].direction, Direction::kOutput);
  EXPECT_EQ(iface->modports[1]->ports[0].name, "b");
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
  EXPECT_EQ(iface->modports[0]->name, "m1");
  EXPECT_EQ(iface->modports[1]->name, "m2");
  EXPECT_EQ(iface->modports[2]->name, "m3");
  EXPECT_EQ(iface->modports[2]->ports[0].direction, Direction::kInout);
}
