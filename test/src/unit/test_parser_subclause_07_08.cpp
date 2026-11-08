#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(AssocArrayParsing, Declaration) {
  auto r = Parse(
      "module t;\n"
      "  int aa[int];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "aa");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
}

TEST(AssocArrayParsing, VectorElementType) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] mem[int];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
}

TEST(AssocArrayParsing, MultipleDeclarations) {
  auto r = Parse(
      "module t;\n"
      "  int a[int];\n"
      "  string b[string];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(AssocArrayParsing, InlineStructTypeAsIndexIsRead) {
  auto r = Parse(
      "module t;\n"
      "  int aa [ struct { int x; } ];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* aa = r.cu->modules[0]->items[0];
  ASSERT_EQ(aa->unpacked_dims.size(), 1u);
  ASSERT_NE(aa->unpacked_dims[0], nullptr);
  EXPECT_EQ(aa->unpacked_dims[0]->kind, ExprKind::kTypeRef);
  ASSERT_NE(aa->unpacked_dims[0]->type_value, nullptr);
  EXPECT_EQ(aa->unpacked_dims[0]->type_value->kind, DataTypeKind::kStruct);
}

TEST(AssocArrayParsing, AssocIndexTypeDimStartsAtItsTypeKeyword) {
  auto r = Parse(
      "module m;\n"
      "  int a [string];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto* dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->text, "string");
  EXPECT_EQ(dim->range.start.line, 2u);
  EXPECT_EQ(dim->range.start.column, 10u);
}

TEST(AssocArrayParsing, AssocIndexTypeKeepsItsPackedDimension) {
  auto r = Parse(
      "module m;\n"
      "  int aa[bit[3:0]];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto* dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->kind, ExprKind::kIdentifier);
  EXPECT_EQ(dim->text, "bit");
  ASSERT_EQ(dim->elements.size(), 1u);
  auto* packed = dim->elements[0];
  ASSERT_NE(packed, nullptr);
  EXPECT_EQ(packed->kind, ExprKind::kBinary);
  EXPECT_EQ(packed->op, TokenKind::kColon);
  ASSERT_NE(packed->lhs, nullptr);
  EXPECT_EQ(packed->lhs->int_val, 3u);
  ASSERT_NE(packed->rhs, nullptr);
  EXPECT_EQ(packed->rhs->int_val, 0u);
}

TEST(AssocArrayParsing, AssocIndexTypeKeepsItsSigningThenItsPackedDimension) {
  auto r = Parse(
      "module m;\n"
      "  int aa[logic signed [7:0]];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto* dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->text, "logic");
  EXPECT_EQ(dim->op, TokenKind::kKwSigned);
  ASSERT_EQ(dim->elements.size(), 1u);
  auto* packed = dim->elements[0];
  ASSERT_NE(packed, nullptr);
  EXPECT_EQ(packed->kind, ExprKind::kBinary);
  EXPECT_EQ(packed->op, TokenKind::kColon);
  ASSERT_NE(packed->lhs, nullptr);
  EXPECT_EQ(packed->lhs->int_val, 7u);
  ASSERT_NE(packed->rhs, nullptr);
  EXPECT_EQ(packed->rhs->int_val, 0u);
}

}  // namespace
