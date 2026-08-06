#include "fixture_parser.h"

using namespace delta;

namespace {

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

TEST(ImplicitNamedPortConnectionParsing,
     ImplicitConnectionDistinctFromEmptyExplicit) {
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

TEST(ImplicitNamedPortConnectionParsing, ImplicitNameSynthesizesSelfReference) {
  // 23.3.2.3: an implicit .name connection is the explicit form .name(name).
  // The parser marks the entry implicit and synthesizes a connection
  // expression that references the identically named signal.
  auto r = Parse("module m; sub u0(.clk); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 1u);
  ASSERT_EQ(item->inst_ports_implicit.size(), 1u);
  EXPECT_TRUE(item->inst_ports_implicit[0]);
  ASSERT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[0].second->kind, ExprKind::kIdentifier);
  EXPECT_EQ(item->inst_ports[0].second->text, "clk");
}

}  // namespace
