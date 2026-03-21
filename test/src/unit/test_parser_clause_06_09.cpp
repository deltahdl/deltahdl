

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

}  // namespace
