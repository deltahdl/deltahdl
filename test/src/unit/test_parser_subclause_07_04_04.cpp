#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(MultidimensionalArrayParsing, UnpackedDimMultiple) {
  auto r = Parse("module m; logic x [3:0][7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 2u);
}
TEST(MultidimensionalArrayParsing, MultidimensionalPackedArray) {
  auto r = Parse(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "joe");
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(MultidimensionalArrayParsing, MultiplePackedDimsBeforeNameAreAllPacked) {
  auto r = Parse("module m; bit [3:0] [7:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->name, "x");
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.extra_packed_dims.size(), 1u);
  EXPECT_TRUE(item->unpacked_dims.empty());
}

TEST(MultidimensionalArrayParsing, CommaListSharesMultiplePackedDims) {
  auto r = Parse(
      "module t;\n"
      "  bit [7:0] [31:0] v7 [1:5] [1:10], v8 [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* v7 = r.cu->modules[0]->items[0];
  auto* v8 = r.cu->modules[0]->items[1];
  EXPECT_EQ(v7->name, "v7");
  EXPECT_EQ(v8->name, "v8");
  EXPECT_EQ(v7->data_type.kind, v8->data_type.kind);
  ASSERT_NE(v7->data_type.packed_dim_left, nullptr);
  ASSERT_NE(v8->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(v7->data_type.packed_dim_left->int_val,
            v8->data_type.packed_dim_left->int_val);
  ASSERT_EQ(v7->data_type.extra_packed_dims.size(), 1u);
  ASSERT_EQ(v8->data_type.extra_packed_dims.size(), 1u);
  EXPECT_EQ(v7->data_type.extra_packed_dims[0].first->int_val,
            v8->data_type.extra_packed_dims[0].first->int_val);
  EXPECT_EQ(v7->unpacked_dims.size(), 2u);
  EXPECT_EQ(v8->unpacked_dims.size(), 1u);
}

TEST(MultidimensionalArrayParsing, ThreeDimUnpackedArray) {
  auto r = Parse(
      "module t;\n"
      "  int A[2][3][4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 3u);
}

}  // namespace
