#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ImplicitNamedPortConnectionParsing, NamedPortWithoutParens) {
  auto r = Parse("module m; sub u0(.clk, .data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "data");
}

TEST(ImplicitNamedPortConnectionParsing, ImplicitAndExplicitNamedPorts) {
  auto r = Parse("module m; sub u0(.a, .b(x), .c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_EQ(item->inst_ports[1].first, "b");
  EXPECT_NE(item->inst_ports[1].second, nullptr);
  EXPECT_EQ(item->inst_ports[2].first, "c");
}

TEST(ImplicitNamedPortConnectionParsing, SingleImplicitNamedPort) {
  auto r = Parse("module m; sub u0(.clk); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 1u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

TEST(ImplicitNamedPortConnectionParsing, ImplicitConnectionDistinctFromEmptyExplicit) {
  auto r_implicit = Parse("module m; sub u0(.a); endmodule\n");
  auto r_explicit = Parse("module m; sub u0(.a()); endmodule\n");
  ASSERT_NE(r_implicit.cu, nullptr);
  ASSERT_NE(r_explicit.cu, nullptr);
  auto* item_implicit = r_implicit.cu->modules[0]->items[0];
  auto* item_explicit = r_explicit.cu->modules[0]->items[0];
  EXPECT_EQ(item_explicit->inst_ports[0].second, nullptr);
  EXPECT_NE(item_implicit->inst_ports[0].second,
            item_explicit->inst_ports[0].second);
}

}  // namespace
