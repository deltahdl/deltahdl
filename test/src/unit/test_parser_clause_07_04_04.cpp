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
TEST(MultidimensionalArrayParsing, MultidimensionalArray) {
  auto r = Parse(
      "module t;\n"
      "  int matrix[4][8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_GE(item->unpacked_dims.size(), 2u);
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

// §7.4.4: Comma-separated declarations share data type and packed dims.
TEST(MultidimensionalArrayParsing, CommaSeparatedDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  bit [7:0] v7 [1:5], v8 [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->name, "v7");
  EXPECT_EQ(i1->name, "v8");
  EXPECT_EQ(i0->data_type.kind, i1->data_type.kind);
  EXPECT_EQ(i0->data_type.packed_dim_left->int_val,
            i1->data_type.packed_dim_left->int_val);
}

// §7.4.4: Three-dimensional unpacked array.
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
