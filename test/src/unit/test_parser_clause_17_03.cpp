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

// --- name_of_instance: with unpacked_dimension (instance array) ---
TEST(ParserAnnexA0414, CheckerInstArray) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0 [3:0] (.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

// --- checker_instantiation: inside another checker ---
TEST(ParserAnnexA0414, CheckerInstInsideChecker) {
  auto r = Parse(
      "checker inner_chk(input logic sig);\n"
      "endchecker\n"
      "checker outer_chk;\n"
      "  logic sig;\n"
      "  inner_chk u0(.sig(sig));\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 2u);
  ASSERT_GE(r.cu->checkers[1]->items.size(), 2u);
  auto* inst = r.cu->checkers[1]->items[1];
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(inst->inst_module, "inner_chk");
  EXPECT_EQ(inst->inst_name, "u0");
}

}  // namespace
