#include "fixture_parser.h"

using namespace delta;

namespace {

// A.4.1.4 checker_instantiation ::=
//     ps_checker_identifier name_of_instance ( [ list_of_checker_port_connections ] ) ;
// Checker instantiation shares the generic instance-parsing path
// (ParseModuleInstList) with module/interface/program instantiation, so the
// parsed item is recorded as kModuleInst. These tests pin every §A.4.1.4
// production and alternative; the sub-symbols (ps_checker_identifier,
// name_of_instance, property_actual_arg, attribute_instance,
// formal_port_identifier) are owned by their respective dependency subclauses.

// list_of_checker_port_connections, alt 1: ordered list with a populated
// property_actual_arg in each ordered_checker_port_connection.
TEST(CheckerInstantiationGrammar, CheckerInstOrderedPorts) {
  auto r = Parse(
      "checker my_chk(input logic a, input logic b, input logic c);\n"
      "endchecker\n"
      "module m; my_chk u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

// list_of_checker_port_connections, alt 2: named list. Each
// named_checker_port_connection uses the `. formal_port_identifier
// ( property_actual_arg )` form.
TEST(CheckerInstantiationGrammar, CheckerInstNamedPorts) {
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

// named_checker_port_connection, form 1 with the optional `( ... )` omitted:
// `. formal_port_identifier`.
TEST(CheckerInstantiationGrammar, CheckerInstNamedPortNoParens) {
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

// named_checker_port_connection, form 1 with empty parens: the inner
// property_actual_arg is itself optional, so `. formal_port_identifier ( )`
// is legal and leaves the connection's actual argument unbound.
TEST(CheckerInstantiationGrammar, CheckerInstNamedEmptyParens) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk(), .rst(rst)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].first, "rst");
  EXPECT_NE(item->inst_ports[1].second, nullptr);
}

// ordered_checker_port_connection with the optional property_actual_arg
// omitted: an empty ordered slot (`a, , c`) is a distinct alternative whose
// actual argument is unbound.
TEST(CheckerInstantiationGrammar, CheckerInstOrderedBlankConnection) {
  auto r = Parse(
      "checker my_chk(input logic a, input logic b, input logic c);\n"
      "endchecker\n"
      "module m; my_chk u0(a, , c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

// Both ordered_checker_port_connection and named_checker_port_connection are
// prefixed by `{ attribute_instance }`. The attribute prefix is accepted and
// the underlying connections still parse.
TEST(CheckerInstantiationGrammar, CheckerInstPortConnectionAttributes) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m;\n"
      "  my_chk u0((* keep *) .clk(clk), (* keep *) .rst(rst));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// ps_checker_identifier name_of_instance ( ... ) ; — pins the item kind and
// the checker/instance identifiers of the simple (unscoped) form.
TEST(CheckerInstantiationGrammar, BasicCheckerInst) {
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

// named_checker_port_connection, form 2: `{ attribute_instance } . *`.
TEST(CheckerInstantiationGrammar, CheckerInstWildcardPort) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

// checker_instantiation with list_of_checker_port_connections omitted: the
// optional connection list reduces to empty parens.
TEST(CheckerInstantiationGrammar, CheckerInstEmptyPorts) {
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

// name_of_instance carries an optional unpacked_dimension.
TEST(CheckerInstantiationGrammar, CheckerInstArray) {
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

// ps_checker_identifier in its package-scoped form (`pkg :: my_chk`).
TEST(CheckerInstantiationGrammar, PackageScopedCheckerInst) {
  auto r = Parse(
      "package pkg;\n"
      "  checker my_chk(input logic clk);\n"
      "  endchecker\n"
      "endpackage\n"
      "module m;\n"
      "  logic clk;\n"
      "  pkg::my_chk u0(.clk(clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_scope, "pkg");
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_EQ(item->inst_name, "u0");
}

// The trailing `;` of checker_instantiation is mandatory.
TEST(CheckerInstantiationGrammar, Error_MissingSemicolon) {
  EXPECT_FALSE(ParseOk(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; my_chk u0() endmodule\n"));
}

// list_of_checker_port_connections is either an all-ordered list or an
// all-named list; the two forms cannot be interleaved in one connection list.
TEST(CheckerInstantiationGrammar, Error_MixedOrderedAndNamedPorts) {
  auto r = Parse(
      "checker my_chk(input logic a, input logic clk);\n"
      "endchecker\n"
      "module m;\n"
      "  logic a, clk;\n"
      "  my_chk u0(a, .clk(clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

}
