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

// §7.8 makes an index type a data_type, A.2.5 writes the index as one, and
// §7.8.5 admits any type with equality defined, an unpacked structure among
// them, so a structure declared in the brackets is read as the index type,
// kept as a type reference holding it. It drew a parse error.
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

// Covers Parser::ParseAssocIndexDim in src/parser/parser_types.cpp, which
// builds the ExprKind::kIdentifier naming an associative array's index type. It
// assigned no range.start before this commit, and src/parser/parser_types.cpp
// assigned none at any site, so a report standing at the dimension printed
// "<unknown location>" instead of a file, line and column. §7.8 writes the
// dimension as `[ index_type ]`, so the node begins at the type keyword:
// `string`, at column 10 of line 2.
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

// Holds that an associative array's index type keeps a packed dimension
// written after it. §7.8 makes an index_type a data_type, and A.2.2.1 writes
// `data_type ::= integer_vector_type [ signing ] { packed_dimension } | ...`,
// so `bit [3:0]` is one index type and the `[` after `bit` opens a dimension
// of that type rather than closing the index. Parser::ParseAssocIndexDim in
// src/parser/parser_types.cpp appends each packed dimension to the dimension
// node's elements as a `[msb:lsb]` range, which is where the range 3:0 is read
// back from.
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

// Holds that an associative array's index type keeps its signing and the
// packed dimension written after it, in that order. A.2.2.1 writes
// `integer_vector_type [ signing ] { packed_dimension }` and §7.8 makes an
// index_type a data_type, so `logic signed [7:0]` is one index type.
// Parser::ParseAssocIndexDim in src/parser/parser_types.cpp reads the signing
// into the dimension node's op and each packed dimension into its elements,
// and a case exercising one of the two alone leaves the order between them
// unasserted, so this one reads both.
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
