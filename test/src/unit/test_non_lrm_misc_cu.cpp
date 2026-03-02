// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST(ParserSection23, PortConnectionEmptyNamed) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(.clk(sys_clk), .unused());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[1].first, "unused");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
}

// =========================================================================
// LRM section 23.1: Module definitions
// =========================================================================
TEST(ParserSection23, ModuleDefinitionEmpty) {
  auto r = Parse("module empty_mod; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "empty_mod");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(ParserSection23, ModuleDefinitionWithBody) {
  auto r = Parse(
      "module m;\n"
      "  wire a;\n"
      "  assign a = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 2);
}

TEST(ParserSection23, MultipleModuleDefinitions) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

// =========================================================================
// LRM section 23.2: Module declarations (ANSI header style)
// =========================================================================
TEST(ParserSection23, AnsiHeaderWithParams) {
  auto r = Parse(
      "module m #(parameter N = 8) (input logic [N-1:0] data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_EQ(mod->params.size(), 1);
  EXPECT_EQ(mod->params[0].first, "N");
  ASSERT_EQ(mod->ports.size(), 1);
  EXPECT_EQ(mod->ports[0].name, "data");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
}

TEST(ParserSection23, AnsiHeaderEmptyParenPorts) {
  auto r = Parse("module m (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

// =========================================================================
// LRM section 23.2.2.1: Non-ANSI port declarations
// =========================================================================
TEST(ParserSection23, NonAnsiInoutPort) {
  auto r = Parse(
      "module m(bus);\n"
      "  inout [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1);
  EXPECT_EQ(mod->ports[0].name, "bus");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(ParserSection23, NonAnsiMultiplePortsSameDir) {
  auto r = Parse(
      "module m(x, y, z);\n"
      "  output x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 3);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(mod->ports[i].direction, Direction::kOutput);
  }
}

// =========================================================================
// LRM section 23.3: Module instances
// =========================================================================
TEST(ParserSection23, SimpleModuleInstance) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u1");
}

TEST(ParserSection23, ModuleInstanceWithParameters) {
  auto r = Parse(
      "module top;\n"
      "  sub #(8, 16) u1 (.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u1");
  ASSERT_EQ(item->inst_params.size(), 2);
}

TEST(ParserSection23, ModuleInstanceEmptyPorts) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_name, "u1");
  EXPECT_TRUE(item->inst_ports.empty());
}

// =========================================================================
// LRM section 23.3.1: Module instance ports (positional connections)
// =========================================================================
TEST(ParserSection23, PositionalPortConnections) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3);
  // Positional ports: first element of pair is empty string_view.
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_TRUE(item->inst_ports[i].first.empty());
    EXPECT_NE(item->inst_ports[i].second, nullptr);
  }
}

TEST(ParserSection23, PositionalPortWithExpression) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (a & b, c | d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
}

// =========================================================================
// LRM section 23.3.2: Port connections
// =========================================================================
TEST(ParserSection23, NamedPortConnectionsOrder) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.b(y), .a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "b");
  EXPECT_EQ(item->inst_ports[1].first, "a");
}

TEST(ParserSection23, NamedPortEmptyConnection) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a(x), .b());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].first, "b");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
}

// =========================================================================
// LRM section 23.3.3: Port connection rules
// =========================================================================
TEST(ParserSection23, PortConnectionRulesNamedMultiple) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.clk(clk), .rst(rst), .data(d), .out(q));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 4);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
  EXPECT_EQ(item->inst_ports[2].first, "data");
  EXPECT_EQ(item->inst_ports[3].first, "out");
}

TEST(ParserSection23, PortConnectionAllEmpty) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a(), .b(), .c());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 3);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->inst_ports[i].second, nullptr);
  }
}

// =========================================================================
// LRM section 23.3.3.7.1: Named port connections .name(expr)
// =========================================================================
TEST(ParserSection23, NamedPortWithPartSelect) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a(bus[7:0]), .b(bus[15:8]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].first, "b");
  EXPECT_NE(item->inst_ports[1].second, nullptr);
}

TEST(ParserSection23, NamedPortWithConcatenation) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.data({a, b, c}));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 1);
  EXPECT_EQ(item->inst_ports[0].first, "data");
  ASSERT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[0].second->kind, ExprKind::kConcatenation);
}

// =========================================================================
// LRM section 23.3.3.7.2: Implicit named port connections (.*)
// =========================================================================
TEST(ParserSection23, WildcardOnly) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_TRUE(item->inst_ports.empty());
}

TEST(ParserSection23, WildcardWithNamedOverrides) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.*, .rst(global_rst), .clk(sys_clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "rst");
  EXPECT_EQ(item->inst_ports[1].first, "clk");
}

TEST(ParserSection23, WildcardWithEmptyPort) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.*, .unused());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 1);
  EXPECT_EQ(item->inst_ports[0].first, "unused");
  EXPECT_EQ(item->inst_ports[0].second, nullptr);
}

}  // namespace
