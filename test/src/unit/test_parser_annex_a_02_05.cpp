#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

const ModuleItem* FindItem(const ParseResult& r, std::string_view name) {
  if (r.cu == nullptr || r.cu->modules.empty()) return nullptr;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->name == name) return item;
  }
  return nullptr;
}

TEST(DeclarationRangeParsing, UnpackedDimensionConstantRange) {
  auto r = Parse("module m; logic a [3:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  ASSERT_NE(a->unpacked_dims[0], nullptr);
  EXPECT_EQ(a->unpacked_dims[0]->kind, ExprKind::kBinary);
  EXPECT_EQ(a->unpacked_dims[0]->op, TokenKind::kColon);
}

TEST(DeclarationRangeParsing, UnpackedDimensionConstantExpressionSize) {
  auto r = Parse("module m; logic a [4]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  ASSERT_NE(a->unpacked_dims[0], nullptr);
  EXPECT_EQ(a->unpacked_dims[0]->kind, ExprKind::kIntegerLiteral);
  EXPECT_NE(a->unpacked_dims[0]->op, TokenKind::kColon);
}

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
  EXPECT_EQ(a->unpacked_dims[0]->rhs, nullptr);
}

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

TEST(DeclarationRangeParsing, UnsizedDimension) {
  auto r = Parse("module m; int a []; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto* a = FindItem(r, "a");
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->unpacked_dims.size(), 1u);
  EXPECT_EQ(a->unpacked_dims[0], nullptr);
}

TEST(DeclarationRangeParsing, VariableDimensionMixedAlternatives) {
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

TEST(DeclarationRangeParsing, QueueDimensionColonWithoutBoundRejected) {
  auto r = Parse("module m; int a [$:]; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(DeclarationRangeParsing, NetTypeIndexIsReported) {
  auto r = Parse(
      "module m;\n"
      "  int a [wire];\n"
      "  int b [supply0];\n"
      "  int c [int];\n"
      "  int d [logic [3:0]];\n"
      "endmodule\n");
  for (uint32_t line : {2u, 3u, 4u, 5u}) {
    EXPECT_EQ(static_cast<bool>(ReportedError(
                  r.diags,
                  "a net type is no data type and cannot index an associative "
                  "array",
                  line, "A.2.5")),
              line < 4u)
        << "line " << line;
  }
}

TEST(DeclarationRangeParsing, DataTypeIndexFormsAreRead) {
  auto r = Parse(
      "class P #(int N = 1); endclass\n"
      "module m;\n"
      "  bit [3:0] k;\n"
      "  int e [enum {A, B}];\n"
      "  int s [struct packed {bit [3:0] f;}];\n"
      "  int u [union packed {bit [3:0] f; bit [3:0] g;}];\n"
      "  int t [type(k)];\n"
      "  int c [P#(8)];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (std::string_view name : {"e", "s", "u", "t", "c"}) {
    const auto* item = FindItem(r, name);
    ASSERT_NE(item, nullptr) << name;
    ASSERT_EQ(item->unpacked_dims.size(), 1u) << name;
    ASSERT_NE(item->unpacked_dims[0], nullptr) << name;
    EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kTypeRef) << name;
    EXPECT_EQ(item->unpacked_dims[0]->type_value == nullptr, name == "t")
        << name;
  }
}

}  // namespace
