#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(WiredNetParsing, WandDecl) {
  auto r = Parse(
      "module t;\n"
      "  wand w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWand);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

TEST(WiredNetParsing, WorDecl) {
  auto r = Parse(
      "module t;\n"
      "  wor w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWor);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

TEST(WiredNetParsing, TriandDecl) {
  auto r = Parse(
      "module t;\n"
      "  triand ta;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTriand);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(WiredNetParsing, TriorDecl) {
  auto r = Parse(
      "module t;\n"
      "  trior to1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrior);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(WiredNetParsing, WandAndTriandIdenticalSyntax) {
  EXPECT_TRUE(ParseOk("module t; wand [7:0] a; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; triand [7:0] a; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; wand a, b; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; triand a, b; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; wand a = 1'b0; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; triand a = 1'b0; endmodule\n"));
}

TEST(WiredNetParsing, WorAndTriorIdenticalSyntax) {
  EXPECT_TRUE(ParseOk("module t; wor [7:0] a; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; trior [7:0] a; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; wor a, b; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; trior a, b; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; wor a = 1'b0; endmodule\n"));
  EXPECT_TRUE(ParseOk("module t; trior a = 1'b0; endmodule\n"));
}

}  // namespace
