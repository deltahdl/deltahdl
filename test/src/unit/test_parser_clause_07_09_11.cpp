#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(AggregateTypeParsing, AssocArrayLiteralWithDefault) {
  auto r = Parse(
      "module t;\n"
      "  string words[int] = '{default: \"hello\"};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AggregateTypeParsing, AssocArrayLiteralKeyValue) {
  auto r = Parse(
      "module t;\n"
      "  integer tab[string] = '{\"Peter\":20, \"Paul\":22, default:-1};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AggregateTypeParsing, AssocArrayLiteralIntKeyedMultipleEntries) {
  auto r = Parse(
      "module t;\n"
      "  int aa[int] = '{3:30, 16'hffff:2, 4'b1000:3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AggregateTypeParsing, AssocArrayLiteralDefaultOnly) {
  auto r = Parse(
      "module t;\n"
      "  int aa[int] = '{default:0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(item->init_expr->pattern_keys.size(), 1u);
  EXPECT_EQ(item->init_expr->pattern_keys[0], "default");
}

TEST(AggregateTypeParsing, AssocArrayLiteralNegativeDefault) {
  auto r = Parse(
      "module t;\n"
      "  integer tab[string] = '{\"a\":1, default:-1};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
