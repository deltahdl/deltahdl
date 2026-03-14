

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DataTypeParsing, LogicPackedDimsEightBit) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
  EXPECT_EQ(item->name, "data");
}

TEST(DataTypeParsing, LogicPackedDimsSixteenBit) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] addr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

TEST(DataTypeParsing, LittleEndianRange) {
  auto r = Parse(
      "module t;\n"
      "  logic [0:7] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 0u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 7u);
}

TEST(DataTypeParsing, NegativeRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [-1:4] b;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, MultipleVectors) {
  auto r = Parse(
      "module t;\n"
      "  logic [4:0] x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (auto* item : items) {
    ASSERT_NE(item->data_type.packed_dim_left, nullptr);
    EXPECT_EQ(item->data_type.packed_dim_left->int_val, 4u);
    ASSERT_NE(item->data_type.packed_dim_right, nullptr);
    EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
  }
}

TEST(DataTypeParsing, RegVectorUnsignedDefault) {
  auto r = Parse(
      "module t;\n"
      "  reg [7:0] r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed);
}

TEST(DataTypeParsing, LogicSignedVector) {
  auto r = Parse(
      "module t;\n"
      "  logic signed [3:0] signed_reg;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 3u);
}

TEST(DataTypeParsing, LrmExamplesScalarAndVector) {
  auto r = Parse(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] v;\n"
      "  logic signed [3:0] signed_reg;\n"
      "  logic [-1:4] b;\n"
      "  wire w1, w2;\n"
      "  logic [4:0] x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
