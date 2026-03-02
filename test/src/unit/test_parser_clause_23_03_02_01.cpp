// §23.3.2.1: Connecting module instance ports by ordered list

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.4 -- Instantiations
// =============================================================================
TEST(ParserAnnexA, A4ModuleInstPositional) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

// =============================================================================
// list_of_port_connections34 ::=
//   ordered_port_connection { , ordered_port_connection }
//   | named_port_connection { , named_port_connection }
// ordered_port_connection ::= { attribute_instance } [ expression ]
// named_port_connection ::=
//   { attribute_instance } . port_identifier [ ( [ expression ] ) ]
//   | { attribute_instance } . *
// A.10 note 34: .* shall appear at most once
// =============================================================================
TEST(ParserAnnexA0411, OrderedPortConnections) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
  // Ordered ports have empty name
  EXPECT_EQ(item->inst_ports[0].first, "");
  EXPECT_EQ(item->inst_ports[1].first, "");
  EXPECT_EQ(item->inst_ports[2].first, "");
}

TEST(ParserAnnexA0411, OrderedPortBlankPosition) {
  // ordered_port_connection ::= { attribute_instance } [ expression ]
  // A blank position (empty optional expression) is valid
  auto r = Parse("module m; sub u0(a, , c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
  EXPECT_NE(item->inst_ports[0].second, nullptr);  // a
  EXPECT_EQ(item->inst_ports[1].second, nullptr);  // blank
  EXPECT_NE(item->inst_ports[2].second, nullptr);  // c
}

// --- interface_instantiation: ordered port connections ---
TEST(ParserAnnexA0412, InterfaceInstOrderedPorts) {
  auto r = Parse("module m; my_if u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

// --- program_instantiation: ordered port connections ---
TEST(ParserAnnexA0413, ProgramInstOrderedPorts) {
  auto r = Parse(
      "program my_prog(input logic a, input logic b, input logic c);\n"
      "endprogram\n"
      "module m; my_prog u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

struct ParseResult4d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4d Parse(const std::string& src) {
  ParseResult4d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Returns the first module item from the first module.
static ModuleItem* FirstItem(ParseResult4d& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// =============================================================================
// §4.6: Ordered (positional) port connections — deterministic mapping
// =============================================================================
TEST(ParserSection4, Sec4_6_OrderedPortConnections) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3u);
  // Positional ports have empty name (first element of pair).
  EXPECT_TRUE(item->inst_ports[0].first.empty());
  EXPECT_TRUE(item->inst_ports[1].first.empty());
  EXPECT_TRUE(item->inst_ports[2].first.empty());
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

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

// =============================================================================
// LRM section 23.10.4 -- Port connection rules (additional)
// =============================================================================
TEST(ParserSection23, PortConnectionPositional) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  ASSERT_EQ(item->inst_ports.size(), 3u);
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

}  // namespace
