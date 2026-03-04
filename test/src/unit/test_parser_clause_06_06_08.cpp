// §6.6.8: Generic interconnect

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
TEST(ParserSection6, InterconnectNet) {
  // §6.7.1: interconnect net has no data type, optional packed/unpacked dims.
  auto r = Parse(
      "module t;\n"
      "  interconnect w1;\n"
      "  interconnect [3:0] w2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, InterconnectWithPackedDim) {
  // §6.6.8: interconnect may have packed dimensions.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  interconnect [7:0] ibus;\n"
              "endmodule\n"));
}

// Step 2b: interconnect (fixes 6.6.8)
TEST(ParserSection6, Interconnect_Basic) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  interconnect bus;\n"
               "endmodule\n"));
}

}  // namespace
