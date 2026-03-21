#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SignedAndUnsigned, DataTypeIntegerAtom) {
  auto r = Parse("module m; int unsigned x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_signed);
}

TEST(SignedAndUnsigned, SigningUnsigned) {
  auto r = Parse("module m; integer unsigned x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->modules[0]->items[0]->data_type.is_signed);
}

TEST(SignedAndUnsigned, DataTypeIntegerVector) {
  auto r = Parse("module m; logic signed [7:0] a; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
}

TEST(SignedAndUnsigned, LogicSignedWithPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  logic signed [15:0] sv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

TEST(SignedAndUnsigned, BitUnsignedWithPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  bit unsigned [7:0] uv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_FALSE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
}

TEST(SignedAndUnsigned, ByteSignedExplicit) {
  auto r = Parse(
      "module t;\n"
      "  byte signed bs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "bs");
}

TEST(SignedAndUnsigned, ByteUnsignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  byte unsigned bu;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "bu");
}

TEST(SignedAndUnsigned, ShortintUnsignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  shortint unsigned su;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "su");
}

TEST(SignedAndUnsigned, LongintUnsignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  longint unsigned lu;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "lu");
}

TEST(SignedAndUnsigned, IntegerUnsignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  integer unsigned iu;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "iu");
}

TEST(SignedAndUnsigned, TimeSignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  time signed ts;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "ts");
}

TEST(SignedAndUnsigned, BitSignedOverride) {
  auto r = Parse(
      "module t;\n"
      "  bit signed bs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "bs");
}

TEST(SignedAndUnsigned, IntUnsignedDecl) {
  auto r = Parse(
      "module m;\n"
      "  int unsigned ui;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "ui");
}

TEST(SignedAndUnsigned, IntSignedDecl) {
  auto r = Parse(
      "module m;\n"
      "  int signed si;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(item->data_type.is_signed);
}

TEST(SignedAndUnsigned, LogicSignedDecl) {
  auto r = Parse(
      "module m;\n"
      "  logic signed [7:0] sv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
}

TEST(SignedAndUnsigned, RegUnsignedDecl) {
  auto r = Parse(
      "module m;\n"
      "  reg unsigned [3:0] ru;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed);
}

TEST(SignedAndUnsigned, IntUnsignedFunctionReturnType) {
  auto r = Parse(
      "class C;\n"
      "  function int unsigned get_val();\n"
      "    int unsigned x;\n"
      "    x = 42;\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_GE(r.cu->classes[0]->members.size(), 1u);
}

TEST(SignedAndUnsigned, RegSignedQualifier) {
  auto r = Parse(
      "module t;\n"
      "  reg signed [7:0] sr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_TRUE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
}

TEST(SignedAndUnsigned, AllTypesExplicitSignedness) {
  auto r = Parse(
      "module t;\n"
      "  byte signed bs;\n"
      "  byte unsigned bu;\n"
      "  shortint signed ss;\n"
      "  shortint unsigned su;\n"
      "  int signed is_;\n"
      "  int unsigned iu;\n"
      "  longint signed ls;\n"
      "  longint unsigned lu;\n"
      "  integer signed igs;\n"
      "  integer unsigned igu;\n"
      "  time signed ts;\n"
      "  time unsigned tu;\n"
      "  logic signed lgs;\n"
      "  logic unsigned lgu;\n"
      "  bit signed bts;\n"
      "  bit unsigned btu;\n"
      "  reg signed rs;\n"
      "  reg unsigned ru;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 18u);

  EXPECT_TRUE(items[0]->data_type.is_signed);
  EXPECT_FALSE(items[1]->data_type.is_signed);

  EXPECT_TRUE(items[2]->data_type.is_signed);
  EXPECT_FALSE(items[3]->data_type.is_signed);

  EXPECT_TRUE(items[4]->data_type.is_signed);
  EXPECT_FALSE(items[5]->data_type.is_signed);

  EXPECT_TRUE(items[6]->data_type.is_signed);
  EXPECT_FALSE(items[7]->data_type.is_signed);

  EXPECT_TRUE(items[8]->data_type.is_signed);
  EXPECT_FALSE(items[9]->data_type.is_signed);

  EXPECT_TRUE(items[10]->data_type.is_signed);
  EXPECT_FALSE(items[11]->data_type.is_signed);

  EXPECT_TRUE(items[12]->data_type.is_signed);
  EXPECT_FALSE(items[13]->data_type.is_signed);

  EXPECT_TRUE(items[14]->data_type.is_signed);
  EXPECT_FALSE(items[15]->data_type.is_signed);

  EXPECT_TRUE(items[16]->data_type.is_signed);
  EXPECT_FALSE(items[17]->data_type.is_signed);
}

TEST(SignedAndUnsigned, RegUnsignedExplicit) {
  auto r = Parse(
      "module t;\n"
      "  reg unsigned [7:0] ru;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
}

TEST(SignedAndUnsigned, IntDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  int x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_TRUE(item->data_type.is_signed) << "int is signed by default";
}

TEST(SignedAndUnsigned, IntExplicitUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  int unsigned x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(item->data_type.is_signed) << "int unsigned is unsigned";
}

TEST(SignedAndUnsigned, ByteDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kByte);
  EXPECT_TRUE(item->data_type.is_signed) << "byte is signed by default";
}

TEST(SignedAndUnsigned, ShortintDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  shortint s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kShortint);
  EXPECT_TRUE(item->data_type.is_signed) << "shortint is signed by default";
}

TEST(SignedAndUnsigned, LongintDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  longint l;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLongint);
  EXPECT_TRUE(item->data_type.is_signed) << "longint is signed by default";
}

TEST(SignedAndUnsigned, IntegerDefaultSigned) {
  auto r = Parse(
      "module t;\n"
      "  integer i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInteger);
  EXPECT_TRUE(item->data_type.is_signed) << "integer is signed by default";
}

TEST(SignedAndUnsigned, TimeDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  time t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_FALSE(item->data_type.is_signed) << "time is unsigned by default";
}

TEST(SignedAndUnsigned, LogicDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  logic l;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->data_type.is_signed) << "logic is unsigned by default";
}

TEST(SignedAndUnsigned, BitDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  bit b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_FALSE(item->data_type.is_signed) << "bit is unsigned by default";
}

TEST(SignedAndUnsigned, RegDefaultUnsigned) {
  auto r = Parse(
      "module t;\n"
      "  reg r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_FALSE(item->data_type.is_signed) << "reg is unsigned by default";
}

TEST(SignedAndUnsigned, SignedVector) {
  auto r = Parse(
      "module t;\n"
      "  logic signed [7:0] sv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(item->data_type.is_signed);
}

TEST(SignedAndUnsigned, UnsignedVector) {
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

}  // namespace
