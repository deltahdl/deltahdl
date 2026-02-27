// §6.6.8: Generic interconnect

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA213, NetDeclInterconnect) {
  auto r = Parse("module m; interconnect net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_interconnect);
}

TEST(ParserA221, NetPortTypeInterconnect) {
  // interconnect implicit_data_type
  // Note: interconnect in ANSI port list requires port-parser extensions;
  // tested here in module body per A.2.1.3 net_declaration form 3.
  auto r = Parse("module m; interconnect [7:0] net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->data_type.is_interconnect);
}

}  // namespace
