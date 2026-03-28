#include "fixture_parser.h"

using namespace delta;

namespace {

// --- R1+R2: packed = before name, unpacked = after name ---

TEST(PackedAndUnpackedArrayParsing, MixedPackedAndUnpackedDims) {
  auto r = Parse("module m; logic [7:0] x [3:0][1:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->unpacked_dims.size(), 2u);
}

TEST(PackedAndUnpackedArrayParsing, PackedOnlyHasNoUnpackedDims) {
  auto r = Parse("module m; bit [7:0] c1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_TRUE(item->unpacked_dims.empty());
}

TEST(PackedAndUnpackedArrayParsing, UnpackedOnlyHasNoPackedDims) {
  auto r = Parse("module m; real u [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

// --- R4: unpacked kinds coexist with packed dims ---

TEST(PackedAndUnpackedArrayParsing, PackedAndDynamicDimension) {
  auto r = Parse("module m; logic [7:0] d []; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
}

TEST(PackedAndUnpackedArrayParsing, PackedAndQueueDimension) {
  auto r = Parse("module m; logic [7:0] q [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
}

TEST(PackedAndUnpackedArrayParsing, PackedAndAssociativeDimension) {
  auto r = Parse("module m; logic [15:0] a [int]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_GE(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "int");
}

// --- R5: unpacked arrays formed from any data type ---

TEST(PackedAndUnpackedArrayParsing, UnpackedArrayOfRealType) {
  auto r = Parse("module m; real u [0:7]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(PackedAndUnpackedArrayParsing, UnpackedArrayOfStringType) {
  auto r = Parse("module m; string s [0:3]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

}  // namespace
