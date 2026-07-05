// Canonical coverage for Annex A §A.2.5 "Declaration ranges".
//
// §A.2.5 owns six pure-syntax productions, all parser-stage:
//   unpacked_dimension   ::= [ constant_range ] | [ constant_expression ]
//   packed_dimension     ::= [ constant_range ] | unsized_dimension
//   associative_dimension::= [ data_type ] | [ * ]
//   variable_dimension   ::= unsized_dimension | unpacked_dimension
//                          | associative_dimension | queue_dimension
//   queue_dimension      ::= [ $ [ : constant_expression ] ]
//   unsized_dimension    ::= [ ]
//
// The packed_dimension range alternative is carried by ParsePackedDims; the
// entire variable_dimension family (and thus the unpacked/associative/queue/
// unsized productions) is carried by ParseUnpackedDims in parser_types.cpp.
// Every dimension is built from a real declaration so the consumed dependency
// constructs (constant_range/constant_expression from §A.8.3, data_type from
// §A.2.2.1) are produced by genuine source syntax.

#include "fixture_parser.h"

using namespace delta;

namespace {

// Returns the first module item with the given declared name, or null.
const ModuleItem* FindItem(const ParseResult& r, std::string_view name) {
  if (r.cu == nullptr || r.cu->modules.empty()) return nullptr;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->name == name) return item;
  }
  return nullptr;
}

// --- unpacked_dimension ::= [ constant_range ] -----------------------------

TEST(DeclarationRangeParsing, UnpackedDimensionConstantRange) {
  auto r = Parse("module m; logic a [3:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  ASSERT_NE(a->unpacked_dims[0], nullptr);
  // constant_range parses to a colon-joined pair.
  EXPECT_EQ(a->unpacked_dims[0]->kind, ExprKind::kBinary);
  EXPECT_EQ(a->unpacked_dims[0]->op, TokenKind::kColon);
}

// --- unpacked_dimension ::= [ constant_expression ] (size form) ------------

TEST(DeclarationRangeParsing, UnpackedDimensionConstantExpressionSize) {
  auto r = Parse("module m; logic a [4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  ASSERT_NE(a->unpacked_dims[0], nullptr);
  // A single constant_expression, not a range.
  EXPECT_EQ(a->unpacked_dims[0]->kind, ExprKind::kIntegerLiteral);
  EXPECT_NE(a->unpacked_dims[0]->op, TokenKind::kColon);
}

// --- packed_dimension ::= [ constant_range ] -------------------------------

TEST(DeclarationRangeParsing, PackedDimensionConstantRange) {
  auto r = Parse("module m; logic [7:0] a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_NE(a->data_type.packed_dim_left, nullptr);
  EXPECT_NE(a->data_type.packed_dim_right, nullptr);
  EXPECT_TRUE(a->data_type.extra_packed_dims.empty());
}

// Repeated packed_dimension (the { packed_dimension } closure in data_type).
TEST(DeclarationRangeParsing, PackedDimensionMultiple) {
  auto r = Parse("module m; logic [7:0][3:0] a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_NE(a->data_type.packed_dim_left, nullptr);
  EXPECT_NE(a->data_type.packed_dim_right, nullptr);
  ASSERT_EQ(a->data_type.extra_packed_dims.size(), 1u);
  EXPECT_NE(a->data_type.extra_packed_dims[0].first, nullptr);
  EXPECT_NE(a->data_type.extra_packed_dims[0].second, nullptr);
}

// --- associative_dimension ::= [ * ] ---------------------------------------

TEST(DeclarationRangeParsing, AssociativeDimensionWildcard) {
  auto r = Parse("module m; int a [*]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  ASSERT_NE(a->unpacked_dims[0], nullptr);
  EXPECT_EQ(a->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(a->unpacked_dims[0]->text, "*");
}

// --- associative_dimension ::= [ data_type ] -------------------------------

TEST(DeclarationRangeParsing, AssociativeDimensionIntegerIndex) {
  auto r = Parse("module m; int a [int]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  ASSERT_NE(a->unpacked_dims[0], nullptr);
  EXPECT_EQ(a->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(a->unpacked_dims[0]->text, "int");
}

// --- queue_dimension ::= [ $ ] (unbounded) ---------------------------------

TEST(DeclarationRangeParsing, QueueDimensionUnbounded) {
  auto r = Parse("module m; int a [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  ASSERT_NE(a->unpacked_dims[0], nullptr);
  EXPECT_EQ(a->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(a->unpacked_dims[0]->text, "$");
  // The optional [ : constant_expression ] bound is omitted.
  EXPECT_EQ(a->unpacked_dims[0]->rhs, nullptr);
}

// --- queue_dimension ::= [ $ : constant_expression ] (bounded) -------------

TEST(DeclarationRangeParsing, QueueDimensionBoundedLiteral) {
  auto r = Parse("module m; int a [$:16]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  ASSERT_NE(a->unpacked_dims[0], nullptr);
  EXPECT_EQ(a->unpacked_dims[0]->text, "$");
  ASSERT_NE(a->unpacked_dims[0]->rhs, nullptr);
  EXPECT_EQ(a->unpacked_dims[0]->rhs->kind, ExprKind::kIntegerLiteral);
}

// --- unsized_dimension ::= [ ] ---------------------------------------------

TEST(DeclarationRangeParsing, UnsizedDimension) {
  auto r = Parse("module m; int a []; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  // An empty dimension is recorded as a null entry.
  EXPECT_EQ(a->unpacked_dims[0], nullptr);
}

// --- variable_dimension dispatch across its four alternatives --------------

TEST(DeclarationRangeParsing, VariableDimensionMixedAlternatives) {
  // One declaration with an unpacked size dim, an associative-wildcard dim,
  // and a queue dim, exercising the dispatch in ParseUnpackedDims.
  auto r = Parse("module m; int a [4][*][$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 3u);
  ASSERT_NE(a->unpacked_dims[0], nullptr);
  EXPECT_EQ(a->unpacked_dims[0]->kind, ExprKind::kIntegerLiteral);
  ASSERT_NE(a->unpacked_dims[1], nullptr);
  EXPECT_EQ(a->unpacked_dims[1]->text, "*");
  ASSERT_NE(a->unpacked_dims[2], nullptr);
  EXPECT_EQ(a->unpacked_dims[2]->text, "$");
}

// --- Negative: queue_dimension colon requires a constant_expression --------

TEST(DeclarationRangeParsing, QueueDimensionColonWithoutBoundRejected) {
  // queue_dimension ::= [ $ [ : constant_expression ] ]: when the colon is
  // present, the bound expression is mandatory.
  auto r = Parse("module m; int a [$:]; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
