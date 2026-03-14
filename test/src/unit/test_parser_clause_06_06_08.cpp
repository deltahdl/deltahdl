#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TypeDeclParsing, NetDeclInterconnect) {
  auto r = Parse("module m; interconnect net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_interconnect);
}

TEST(NetAndVariableTypeParsing, NetPortTypeInterconnect) {
  auto r = Parse("module m; interconnect [7:0] net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->data_type.is_interconnect);
}
TEST(DataTypeParsing, InterconnectNet) {
  auto r = Parse(
      "module t;\n"
      "  interconnect w1;\n"
      "  interconnect [3:0] w2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(DataTypeParsing, InterconnectWithPackedDim) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  interconnect [7:0] ibus;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, Interconnect_Basic) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  interconnect bus;\n"
               "endmodule\n"));
}

}  // namespace
