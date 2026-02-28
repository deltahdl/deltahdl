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

}  // namespace
