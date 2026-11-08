#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

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

TEST(CheckerInstantiationGrammar, PackageScopedCheckerInst) {
  auto r = Parse(
      "package pkg;\n"
      "  checker my_chk(input logic clk);\n"
      "  endchecker\n"
      "endpackage\n"
      "module m;\n"
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

TEST(CheckerInstantiationGrammar, Error_MissingSemicolon) {
  auto r = Parse(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; my_chk u0() endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "23.3.2"));
}

TEST(CheckerInstantiationGrammar, Error_MixedOrderedAndNamedPorts) {
  auto r = Parse(
      "checker my_chk(input logic a, input logic clk);\n"
      "endchecker\n"
      "module m;\n"
      "  logic a, clk;\n"
      "  my_chk u0(a, .clk(clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "ordered and named port connections cannot be mixed", 5,
      "23.3.2"));
}

TEST(CheckerInstantiationGrammar, InstanceListContinuationIsRecorded) {
  auto r = Parse(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  chk c1(s), c2(t);\n"
      "  chk c3(u);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_FALSE(items[0]->inst_continues_list);
  EXPECT_TRUE(items[1]->inst_continues_list);
  EXPECT_FALSE(items[2]->inst_continues_list);
}

}  // namespace
