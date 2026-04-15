#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- R1: .* implicitly connects all ports where name and type match ---

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

TEST(WildcardPortConnectionParsing, WildcardWithDefinedChildModule) {
  auto r = Parse(
      "module sub(input a, input b, output c);\n"
      "endmodule\n"
      "module m;\n"
      "  logic a, b, c;\n"
      "  sub u1(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(WildcardPortConnectionParsing, WildcardMultipleChildPorts) {
  auto r = Parse(
      "module sub(input a, input b, input c, output d, output e);\n"
      "endmodule\n"
      "module m;\n"
      "  logic a, b, c, d, e;\n"
      "  sub u1(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_wildcard);
  EXPECT_TRUE(inst->inst_ports.empty());
}

// --- R2: Named connections can mix with .* to override or leave ports
//         unconnected ---

TEST(WildcardPortConnectionParsing, WildcardWithNamedPorts) {
  auto r = Parse("module m; sub u0(.clk(clk), .*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_EQ(item->inst_ports.size(), 1u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

TEST(WildcardPortConnectionParsing, WildcardWithNamedOverrides) {
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

TEST(WildcardPortConnectionParsing, WildcardWithNamedOverrideAndDefinedChild) {
  auto r = Parse(
      "module sub(input a, input b, output c);\n"
      "endmodule\n"
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  sub u1(.a(d), .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(WildcardPortConnectionParsing, WildcardWithMultipleEmptyPorts) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(.*, .a(), .b());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_EQ(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].first, "b");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
}

// --- R5: .* may appear anywhere in the port list ---

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

// --- R5 (attribute interaction) ---

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

// --- R5 (with parameter and instance array) ---

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

// --- R6: .* shall appear at most once (error condition) ---

TEST(WildcardPortConnectionParsing, WildcardCannotMixWithPositional) {
  auto r = Parse(
      "module top;\n"
      "  sub u1(a, .*);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// --- R7: Different instances in same parent can mix connection styles ---

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
