#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PackedUnionParsing, UnionSoftQualifier) {
  auto r = Parse(
      "module m;\n"
      "  union soft { int a; real b; } u;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_soft);
}
TEST(PackedUnionParsing, UnionSoftPacked) {
  auto r = Parse(
      "module t;\n"
      "  typedef union soft packed {\n"
      "    bit [7:0] a;\n"
      "    bit [3:0] b;\n"
      "  } soft_u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_soft);
  EXPECT_TRUE(item->typedef_type.is_packed);
}

TEST(PackedUnionParsing, UnionPacked) {
  auto r = Parse(
      "module t;\n"
      "  typedef union packed {\n"
      "    logic [31:0] word;\n"
      "    logic [3:0] [7:0] bytes;\n"
      "  } word_u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_EQ(item->typedef_type.struct_members.size(), 2u);
}

TEST(PackedUnionParsing, TwoLogicMembers) {
  auto r = Parse(
      "module m;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §7.3.1: packed union with signed qualifier.
TEST(PackedUnionParsing, PackedSignedQualifier) {
  auto r = Parse(
      "module m;\n"
      "  union packed signed { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_TRUE(item->data_type.is_signed);
}

// §7.3.1: packed union with explicit unsigned qualifier.
TEST(PackedUnionParsing, PackedUnsignedExplicit) {
  auto r = Parse(
      "module m;\n"
      "  union packed unsigned { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_FALSE(item->data_type.is_signed);
}

// §7.3.1: soft qualifier implies packed; parser records is_soft.
TEST(PackedUnionParsing, SoftWithoutPackedKeyword) {
  auto r = Parse(
      "module m;\n"
      "  union soft { logic [7:0] a; logic [15:0] b; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_soft);
}

}  // namespace
