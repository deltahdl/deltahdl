#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PackedArrayParsing, PackedDimConstantRange) {
  auto r = Parse("module m; logic [7:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(PackedArrayParsing, PackedDimMultiple) {
  auto r = Parse("module m; logic [3:0][7:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.extra_packed_dims.size(), 1u);
}

TEST(PackedArrayParsing, MultiplePackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0][7:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 3u);
  EXPECT_FALSE(item->data_type.extra_packed_dims.empty());
}

TEST(PackedArrayParsing, PackedArrayMultiDim) {
  auto r = Parse(
      "module t;\n"
      "  bit [3:0][7:0] packed_2d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "packed_2d");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
}

TEST(PackedArrayParsing, ConstantRangeInPackedDim) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

TEST(PackedArrayParsing, ConstantBitSelectPackedDim) {
  auto r = Parse("module m; logic [7:0] data; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackedArrayParsing, SingleNumberDimIsError) {
  auto r = Parse("module m; logic [8] x; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PackedArrayParsing, SignedPackedArray) {
  auto r = Parse(
      "module m;\n"
      "  logic signed [7:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
}

}  // namespace
