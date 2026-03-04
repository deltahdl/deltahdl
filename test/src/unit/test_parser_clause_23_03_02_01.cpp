#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A4ModuleInstPositional) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(ParserAnnexA0411, OrderedPortConnections) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);

  EXPECT_EQ(item->inst_ports[0].first, "");
  EXPECT_EQ(item->inst_ports[1].first, "");
  EXPECT_EQ(item->inst_ports[2].first, "");
}

TEST(ParserAnnexA0411, OrderedPortBlankPosition) {

  auto r = Parse("module m; sub u0(a, , c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

TEST(ParserAnnexA0412, InterfaceInstOrderedPorts) {
  auto r = Parse("module m; my_if u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

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

  EXPECT_TRUE(item->inst_ports[0].first.empty());
  EXPECT_TRUE(item->inst_ports[1].first.empty());
  EXPECT_TRUE(item->inst_ports[2].first.empty());
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

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

TEST(ParserSection23, PositionalPortConnections) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3);

  for (size_t i = 0; i < 3; ++i) {
    EXPECT_TRUE(item->inst_ports[i].first.empty());
    EXPECT_NE(item->inst_ports[i].second, nullptr);
  }
}

TEST(ParserSection23, PositionalPortWithExpression) {
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

}
