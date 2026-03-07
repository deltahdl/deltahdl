// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection6, Sec6_11_LogicPackedDims) {
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

TEST(ParserSection6, Sec6_5_LogicPackedDims) {
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

TEST(ParserSection6, UnsignedVector) {
  auto r = Parse(
      "module t;\n"
      "  logic unsigned [15:0] uv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "uv");
}

// §6.9: Scalar — no range specification, 1-bit wide.
TEST(ParserSection6, Sec6_9_ScalarNoRange) {
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

// §6.9.1: Little-endian range [0:7].
TEST(ParserSection6, Sec6_9_1_LittleEndianRange) {
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

// §6.9.1: Negative range [-1:4] — 6-bit vector.
TEST(ParserSection6, Sec6_9_1_NegativeRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [-1:4] b;\n"
              "endmodule\n"));
}

// §6.9.1: Multiple vector declarations with shared range.
TEST(ParserSection6, Sec6_9_1_MultipleVectors) {
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

// §6.9.1: Vector of reg is treated as unsigned by default.
TEST(ParserSection6, Sec6_9_1_RegVectorUnsignedDefault) {
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

// §6.9.1: Vector explicitly declared signed.
TEST(ParserSection6, Sec6_9_1_LogicSignedVector) {
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

// §6.9: LRM examples — wand w, tri [15:0] busa, etc.
TEST(ParserSection6, Sec6_9_LrmExamplesScalarAndVector) {
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
