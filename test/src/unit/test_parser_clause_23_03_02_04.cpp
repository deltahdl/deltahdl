#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(WildcardPortConnectionParsing, WildcardOnly) {
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

TEST(WildcardPortConnectionParsing, WildcardWithEmptyPort) {
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

TEST(WildcardPortConnectionParsing, WildcardBeforeNamed) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(.*, .clk(sys_clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 1u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

TEST(WildcardPortConnectionParsing, WildcardAfterNamed) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(.clk(sys_clk), .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 1u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

TEST(WildcardPortConnectionParsing, WildcardBetweenNamed) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(.a(x), .*, .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_EQ(item->inst_ports[1].first, "b");
}

TEST(WildcardPortConnectionParsing, AttributeOnWildcardPort) {
  auto r = Parse(
      "module m;\n"
      "  sub u0(.clk(clk), (* synthesis_off *) .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_EQ(item->inst_ports.size(), 1u);
}

TEST(WildcardPortConnectionParsing, ParametersArrayAndWildcardCombined) {
  auto r = Parse(
      "module m;\n"
      "  sub #(.W(8)) u0[3:0](.clk(clk), .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
  EXPECT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
  EXPECT_EQ(item->inst_ports.size(), 1u);
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(WildcardPortConnectionParsing, WildcardAppearsAtMostOnce) {
  // §23.3.2.4: the .* token pair may appear at most once in the port list.
  auto r = Parse(
      "module top;\n"
      "  sub u1(.*, .clk(c), .*);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(WildcardPortConnectionParsing, WildcardCannotMixWithPositional) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(a, .*);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(WildcardPortConnectionParsing, MixedStylesInSameParent) {
  auto r = Parse(
      "module sub(input a, output b); endmodule\n"
      "module top;\n"
      "  logic a, b, c, d;\n"
      "  sub u0(a, b);\n"
      "  sub u1(.a(c), .b(d));\n"
      "  sub u2(.a, .b);\n"
      "  sub u3(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[1]->items;
  ASSERT_GE(items.size(), 4u);
  EXPECT_FALSE(items[0]->inst_wildcard);
  EXPECT_FALSE(items[1]->inst_wildcard);
  EXPECT_FALSE(items[2]->inst_wildcard);
  EXPECT_TRUE(items[3]->inst_wildcard);
}

}  // namespace
