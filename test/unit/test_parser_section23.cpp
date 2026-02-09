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

// --- Non-ANSI port declarations (LRM §23.2.2.1) ---

TEST(ParserSection23, NonAnsiPortsBasic) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
}

TEST(ParserSection23, NonAnsiPortsWithTypes) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input [7:0] a;\n"
      "  output reg b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[1].data_type.kind, DataTypeKind::kReg);
}

TEST(ParserSection23, NonAnsiPortsMixed) {
  auto r = Parse(
      "module m(a, b, c, d);\n"
      "  input a, b;\n"
      "  output [3:0] c;\n"
      "  inout d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 4);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[1].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[2].name, "c");
  EXPECT_EQ(mod->ports[2].direction, Direction::kOutput);
  EXPECT_NE(mod->ports[2].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(mod->ports[3].name, "d");
  EXPECT_EQ(mod->ports[3].direction, Direction::kInout);
}

// --- Wildcard .* port connections (LRM §23.3.2.4) ---

TEST(ParserSection23, WildcardConnection) {
  auto r = Parse(
      "module top;\n"
      "  sub m1(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "m1");
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(ParserSection23, WildcardWithNamed) {
  auto r = Parse(
      "module top;\n"
      "  sub m1(.*, .clk(sys_clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 1);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

// --- Extern module declarations (LRM §23.2.1) ---

TEST(ParserSection23, ExternModule) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "foo");
  EXPECT_TRUE(mod->is_extern);
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_TRUE(mod->items.empty());
}

TEST(ParserSection23, ExternModuleNoBody) {
  auto r = Parse(
      "extern module bar(input logic x);\n"
      "module baz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
  EXPECT_TRUE(r.cu->modules[0]->is_extern);
  EXPECT_EQ(r.cu->modules[1]->name, "baz");
  EXPECT_FALSE(r.cu->modules[1]->is_extern);
}

// --- Instance arrays (LRM §23.3.2) ---

TEST(ParserSection23, InstanceArray) {
  auto r = Parse(
      "module top;\n"
      "  sub inst[3:0] (.a(a), .b(b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "inst");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

TEST(ParserSection23, InstanceArraySingle) {
  auto r = Parse(
      "module top;\n"
      "  sub inst[8] (.a(a));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_name, "inst");
  EXPECT_NE(item->inst_range_left, nullptr);
  // Single dimension: only left is set, right is nullptr.
  EXPECT_EQ(item->inst_range_right, nullptr);
}
