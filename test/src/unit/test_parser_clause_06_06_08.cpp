#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(InterconnectParsing, BasicDecl) {
  EXPECT_TRUE(ParseOk("module m; interconnect ic; endmodule"));
}

TEST(InterconnectParsing, DeclSetsFlag) {
  auto r = Parse("module m; interconnect net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_interconnect);
}

TEST(InterconnectParsing, WithPackedDim) {
  auto r = Parse("module m; interconnect [7:0] net1; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->data_type.is_interconnect);
}

TEST(InterconnectParsing, MultipleDecls) {
  auto r = Parse(
      "module t;\n"
      "  interconnect w1;\n"
      "  interconnect [3:0] w2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(InterconnectParsing, PackedDimParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  interconnect [7:0] ibus;\n"
              "endmodule\n"));
}

TEST(InterconnectParsing, BasicWithVersionGate) {
  EXPECT_TRUE(
      ParseOk6("module t;\n"
               "  interconnect bus;\n"
               "endmodule\n"));
}

TEST(InterconnectParsing, DeclFlagWithPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  interconnect ibus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_EQ(item->name, "ibus");
}

TEST(InterconnectParsing, SignedQualifier) {
  auto r = Parse("module m; interconnect signed [7:0] s; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_TRUE(item->data_type.is_signed);
}

TEST(InterconnectParsing, UnsignedQualifier) {
  auto r = Parse("module m; interconnect unsigned [7:0] u; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_interconnect);
  EXPECT_FALSE(item->data_type.is_signed);
}

TEST(InterconnectParsing, MultipleNetsOneLine) {
  auto r = Parse("module m; interconnect a, b, c; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 3u);
}

}  // namespace
