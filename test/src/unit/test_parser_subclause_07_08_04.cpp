#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(IntegralIndexAssocArrayParsing, AssocDimByteType) {
  auto r = Parse("module m; int aa [byte]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "byte");
}
TEST(IntegralIndexAssocArrayParsing, AssocArrayIntIndex) {
  auto r = Parse(
      "module t;\n"
      "  byte lookup[int];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "lookup");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(item->unpacked_dims[0]->text, "int");
}

TEST(IntegralIndexAssocArrayParsing, AssocArrayIntegerIndex) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] cache[integer];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cache");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "integer");
}

TEST(IntegralIndexAssocArrayParsing, AssocDimByteUnsignedType) {
  auto r = Parse("module m; int aa [byte unsigned]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "byte");
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kKwUnsigned);
}

TEST(IntegralIndexAssocArrayParsing, AssocDimIntSignedType) {
  auto r = Parse("module m; int aa [int signed]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kKwSigned);
}

TEST(IntegralIndexAssocArrayParsing, AssocDimStringTakesNoSigning) {
  auto r = Parse("module m; int aa [string unsigned]; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']', got 'unsigned'", 1, "7.8"));
}

TEST(IntegralIndexAssocArrayParsing, AssocDimByteRecordsNoSigningByDefault) {
  auto r = Parse("module m; int aa [byte]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kEof);
}

}  // namespace
