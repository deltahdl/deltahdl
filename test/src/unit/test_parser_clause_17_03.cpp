// §17.3: Checker instantiation

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.4.1.4 -- Checker instantiation
//
// checker_instantiation ::=
//   ps_checker_identifier name_of_instance
//     ( [ list_of_checker_port_connections ] ) ;
//
// list_of_checker_port_connections ::=
//   ordered_checker_port_connection { , ordered_checker_port_connection }
//   | named_checker_port_connection { , named_checker_port_connection }
//
// ordered_checker_port_connection ::=
//   { attribute_instance } [ property_actual_arg ]
//
// named_checker_port_connection ::=
//   { attribute_instance } . formal_port_identifier
//     [ ( [ property_actual_arg ] ) ]
//   | { attribute_instance } . *
// =============================================================================
// --- checker_instantiation: basic named port connections ---
TEST(ParserAnnexA0414, BasicCheckerInst) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic data);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk(clk), .data(data)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- named_checker_port_connection: .* (wildcard) ---
TEST(ParserAnnexA0414, CheckerInstWildcardPort) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

// --- list_of_checker_port_connections: empty ---
TEST(ParserAnnexA0414, CheckerInstEmptyPorts) {
  auto r = Parse(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; my_chk u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

}  // namespace
