#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA25, UnpackedDimensionConstantRange) {
  auto r = Parse("module m; logic x [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kBinary);
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kColon);
}

TEST(ParserA25, UnpackedDimensionConstantExpr) {
  auto r = Parse("module m; logic x [8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(item->unpacked_dims[0]->int_val, 8u);
}

TEST(ParserA25, MultipleUnpackedDimensions) {
  auto r = Parse("module m; logic x [3:0][7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->unpacked_dims.size(), 2u);
}

TEST(ParserA25, PackedDimensionConstantRange) {
  auto r = Parse("module m; logic [15:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ParserA25, PackedDimensionMultiple) {
  auto r = Parse("module m; logic [3:0][7:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_GE(item->data_type.extra_packed_dims.size(), 1u);
}

TEST(ParserA25, UnsizedDimension) {
  auto r = Parse("module m; logic x []; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
}

TEST(ParserA25, AssociativeDimensionWildcard) {
  auto r = Parse("module m; int x [*]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "*");
}

TEST(ParserA25, AssociativeDimensionWithType) {
  auto r = Parse("module m; int x [string]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "string");
}

TEST(ParserA25, AssociativeDimensionWithIntType) {
  auto r = Parse("module m; string x [int]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "int");
}

TEST(ParserA25, QueueDimensionUnbounded) {
  auto r = Parse("module m; int x [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  EXPECT_EQ(item->unpacked_dims[0]->rhs, nullptr);
}

TEST(ParserA25, QueueDimensionBounded) {
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

TEST(ParserA25, VariableDimensionOnFuncArg) {
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

TEST(ParserA25, MixedPackedAndUnpackedDims) {
  auto r = Parse("module m; logic [7:0] x [3:0][1:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->unpacked_dims.size(), 2u);
}

TEST(ParserA25, ParamWithUnpackedDims) {
  auto r = Parse("module m; parameter int P [1:0] = '{0, 1}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

}  // namespace
