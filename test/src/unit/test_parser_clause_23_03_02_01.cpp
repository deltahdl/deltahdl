#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleInstantiationGrammar, ModuleInstPositional) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(ModuleInstantiationGrammar, OrderedPortBlankPosition) {
  auto r = Parse("module m; sub u0(a, , c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

TEST(ModuleInstantiationGrammar, OrderedPortConnectionsParsed) {
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

  EXPECT_TRUE(item->inst_ports[0].first.empty());
  EXPECT_TRUE(item->inst_ports[1].first.empty());
  EXPECT_TRUE(item->inst_ports[2].first.empty());
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

TEST(ModuleInstantiationGrammar, PositionalPortWithExpression) {
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

TEST(ModuleInstantiationGrammar, AttributeOnOrderedPort) {
  auto r = Parse(
      "module m;\n"
      "  sub u0((* keep *) a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
}

TEST(ModuleInstantiationGrammar, MultipleConsecutiveBlankPorts) {
  auto r = Parse("module m; sub u0(a, , , b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 4u);
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
  EXPECT_EQ(item->inst_ports[2].second, nullptr);
  EXPECT_NE(item->inst_ports[3].second, nullptr);
}

TEST(ModuleInstantiationGrammar, AllBlankOrderedPorts) {
  auto r = Parse("module m; sub u0(, , ); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_TRUE(item->inst_ports[i].first.empty());
    EXPECT_EQ(item->inst_ports[i].second, nullptr);
  }
}

TEST(ModuleInstantiationGrammar, SingleOrderedPort) {
  auto r = Parse("module m; sub u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 1u);
  EXPECT_TRUE(item->inst_ports[0].first.empty());
  EXPECT_NE(item->inst_ports[0].second, nullptr);
}

TEST(ModuleInstantiationGrammar, OrderedPortWithConcatenation) {
  auto r = Parse("module m; sub u0({a, b}, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_TRUE(item->inst_ports[0].first.empty());
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[0].second->kind, ExprKind::kConcatenation);
}

TEST(ModuleInstantiationGrammar, LeadingBlankOrderedPort) {
  auto r = Parse("module m; sub u0(, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_EQ(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

TEST(ModuleInstantiationGrammar, TrailingBlankOrderedPort) {
  auto r = Parse("module m; sub u0(a, b, ); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
  EXPECT_EQ(item->inst_ports[2].second, nullptr);
}

TEST(ModuleInstantiationGrammar, OrderedPortWithTernaryExpression) {
  auto r = Parse("module m; sub u0(sel ? a : b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
}

}  // namespace
