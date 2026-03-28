#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DeclarationRangeParsing, UnpackedDimensionConstantRange) {
  auto r = Parse("module m; logic x [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kBinary);
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kColon);
}

TEST(DeclarationRangeParsing, UnpackedDimensionConstantExpr) {
  auto r = Parse("module m; logic x [8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(item->unpacked_dims[0]->int_val, 8u);
}

TEST(DeclarationRangeParsing, MultipleUnpackedDimensions) {
  auto r = Parse("module m; logic x [3:0][7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->unpacked_dims.size(), 2u);
}

TEST(DeclarationRangeParsing, PackedDimensionConstantRange) {
  auto r = Parse("module m; logic [15:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(DeclarationRangeParsing, PackedDimensionMultiple) {
  auto r = Parse("module m; logic [3:0][7:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_GE(item->data_type.extra_packed_dims.size(), 1u);
}

TEST(DeclarationRangeParsing, UnsizedDimension) {
  auto r = Parse("module m; logic x []; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
}

TEST(DeclarationRangeParsing, AssociativeDimensionWildcard) {
  auto r = Parse("module m; int x [*]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "*");
}

TEST(DeclarationRangeParsing, AssociativeDimensionWithType) {
  auto r = Parse("module m; int x [string]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "string");
}

TEST(DeclarationRangeParsing, AssociativeDimensionWithIntType) {
  auto r = Parse("module m; string x [int]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "int");
}

TEST(DeclarationRangeParsing, QueueDimensionUnbounded) {
  auto r = Parse("module m; int x [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  EXPECT_EQ(item->unpacked_dims[0]->rhs, nullptr);
}

TEST(DeclarationRangeParsing, QueueDimensionBounded) {
  auto r = Parse("module m; int x [$:255]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  ASSERT_NE(item->unpacked_dims[0]->rhs, nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->rhs->int_val, 255u);
}

TEST(DeclarationRangeParsing, VariableDimensionOnFuncArg) {
  auto r = Parse(
      "module m;\n"
      "  function void f(int x [3:0]);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->func_args.size(), 1u);
  EXPECT_GE(item->func_args[0].unpacked_dims.size(), 1u);
}

TEST(DeclarationRangeParsing, ParamWithUnpackedDims) {
  auto r = Parse("module m; parameter int P [1:0] = '{0, 1}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

// --- unpacked_dimension edge cases ---

TEST(DeclarationRangeParsing, UnpackedDimensionAscendingRange) {
  auto r = Parse("module m; logic x [0:7]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kBinary);
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kColon);
}

TEST(DeclarationRangeParsing, UnpackedDimensionOnPort) {
  auto r = Parse("module m(input logic x [3:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_GE(r.cu->modules[0]->ports[0].unpacked_dims.size(), 1u);
}

TEST(DeclarationRangeParsing, UnpackedDimensionOnNet) {
  auto r = Parse("module m; wire w [3:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

// --- associative_dimension with other built-in types ---

TEST(DeclarationRangeParsing, AssociativeDimensionByteType) {
  auto r = Parse("module m; int x [byte]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "byte");
}

TEST(DeclarationRangeParsing, AssociativeDimensionShortintType) {
  auto r = Parse("module m; int x [shortint]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "shortint");
}

TEST(DeclarationRangeParsing, AssociativeDimensionLongintType) {
  auto r = Parse("module m; int x [longint]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "longint");
}

TEST(DeclarationRangeParsing, AssociativeDimensionIntegerType) {
  auto r = Parse("module m; int x [integer]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "integer");
}

// --- variable_dimension all alternatives ---

TEST(DeclarationRangeParsing, VariableDimensionUnsized) {
  auto r = Parse(
      "module m;\n"
      "  function void f(int x []);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->func_args.size(), 1u);
  ASSERT_GE(item->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(item->func_args[0].unpacked_dims[0], nullptr);
}

TEST(DeclarationRangeParsing, VariableDimensionAssociative) {
  auto r = Parse(
      "module m;\n"
      "  function void f(int x [string]);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->func_args.size(), 1u);
  ASSERT_GE(item->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(item->func_args[0].unpacked_dims[0]->text, "string");
}

TEST(DeclarationRangeParsing, VariableDimensionQueue) {
  auto r = Parse(
      "module m;\n"
      "  function void f(int x [$]);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->func_args.size(), 1u);
  ASSERT_GE(item->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(item->func_args[0].unpacked_dims[0]->text, "$");
}

// --- packed_dimension on struct member ---

TEST(DeclarationRangeParsing, PackedDimensionOnStructMember) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] data; } my_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
