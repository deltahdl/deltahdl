

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ScalarAndVectorDeclaration, ScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  logic a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, RegScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  reg a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, BitScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  bit a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, RangeProducesDimensions) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, RegRangeProducesDimensions) {
  auto r = Parse(
      "module t;\n"
      "  reg [3:0] r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, BitRangeProducesDimensions) {
  auto r = Parse(
      "module t;\n"
      "  bit [3:0] b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

// §6.9: An object declared implicitly as logic without a range is a scalar.
// The parser shall leave the packed-dimension fields null for `var v;`.
TEST(ScalarAndVectorDeclaration, ImplicitLogicScalarHasNoPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  var v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

// §6.9: The multibit-vector rule applies to implicit logic; a `var [7:0] v;`
// declaration shall carry a packed range and parse as a vector.
TEST(ScalarAndVectorDeclaration, ImplicitLogicVectorHasPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  var [7:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

}  // namespace
