#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA25, PackedAndUnpackedDims) {
  auto r = Parse("module m; logic [7:0] mem [0:255]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(ParserSection6, Sec6_11_LogicPackedAndUnpackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mem[256];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserSection6, Sec6_11_PackedAndUnpackedWithRange) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_FALSE(item->unpacked_dims.empty());
  EXPECT_EQ(item->name, "mem");
}

TEST(ParserSection7, PackedArrayWithUnpacked) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mem [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "mem");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

TEST(ParserSection7, MemoryDeclaration_Type) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mema [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "mema");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(ParserSection7, MemoryDeclaration_Dim) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mema [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto* dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->kind, ExprKind::kBinary);
  EXPECT_EQ(dim->op, TokenKind::kColon);
}
TEST(ParserSection6, VectorWithMultipleDims) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] mem [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->name, "mem");
}

}  // namespace
