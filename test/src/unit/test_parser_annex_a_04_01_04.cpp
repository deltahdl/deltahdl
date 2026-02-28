// Annex A.4.1.4: Checker instantiation

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- ordered_checker_port_connection ---
TEST(ParserAnnexA0414, CheckerInstOrderedPorts) {
  auto r = Parse(
      "checker my_chk(input logic a, input logic b, input logic c);\n"
      "endchecker\n"
      "module m; my_chk u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

// --- named_checker_port_connection: .port_identifier(property_actual_arg) ---
TEST(ParserAnnexA0414, CheckerInstNamedPorts) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk(clk), .rst(rst)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// --- named_checker_port_connection: .port_identifier (no parentheses) ---
TEST(ParserAnnexA0414, CheckerInstNamedPortNoParens) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

}  // namespace
