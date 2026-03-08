#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection6, WireDecl) {
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWire);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

TEST(ParserSection6, TriDecl) {
  auto r = Parse(
      "module t;\n"
      "  tri t0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "t0");
}

TEST(ParserSection6, WireAndTriBothAreNets) {
  auto r = Parse(
      "module t;\n"
      "  wire a;\n"
      "  tri b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_TRUE(items[1]->data_type.is_net);
}

TEST(ParserSection6, WireVectorDecl) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWire);
  EXPECT_EQ(item->name, "bus");
}

TEST(ParserSection6, TriVectorDecl) {
  auto r = Parse(
      "module t;\n"
      "  tri [3:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_EQ(item->name, "bus");
}

TEST(ParserSection6, WireDeclWithAssign) {
  auto r = Parse(
      "module t;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection6, WireMultipleDeclarators) {
  auto r = Parse(
      "module t;\n"
      "  wire a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserSection6, WireAndTriIdenticalSyntax) {
  EXPECT_TRUE(ParseOk("module t; wire [7:0] a; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; tri [7:0] a; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; wire a, b; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; tri a, b; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; wire a = 1'b0; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; tri a = 1'b0; endmodule\n"));
}

}
