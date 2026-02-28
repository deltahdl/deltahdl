// Annex A.2.2.1: Net and variable types

#include "fixture_parser.h"

using namespace delta;

namespace {

// non_integer_type
TEST(ParserA221, DataTypeNonInteger) {
  auto r = Parse("module m; real x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kReal);
}

// --- integer_vector_type ---
// bit | logic | reg
TEST(ParserA221, IntegerVectorTypes) {
  auto r = Parse(
      "module m;\n"
      "  bit a;\n"
      "  logic b;\n"
      "  reg c;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(r.cu->modules[0]->items[1]->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(r.cu->modules[0]->items[2]->data_type.kind, DataTypeKind::kReg);
}

// --- net_type ---
// supply0|supply1|tri|triand|trior|trireg|tri0|tri1|uwire|wire|wand|wor
TEST(ParserA221, NetTypeVariants) {
  auto r = Parse(
      "module m;\n"
      "  supply0 s0;\n"
      "  supply1 s1;\n"
      "  tri t;\n"
      "  triand ta;\n"
      "  trior to2;\n"
      "  trireg tr;\n"
      "  tri0 t0;\n"
      "  tri1 t1;\n"
      "  uwire uw;\n"
      "  wire w;\n"
      "  wand wa;\n"
      "  wor wo;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kSupply0);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kSupply1);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kTri);
  EXPECT_EQ(items[3]->data_type.kind, DataTypeKind::kTriand);
  EXPECT_EQ(items[4]->data_type.kind, DataTypeKind::kTrior);
  EXPECT_EQ(items[5]->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(items[6]->data_type.kind, DataTypeKind::kTri0);
  EXPECT_EQ(items[7]->data_type.kind, DataTypeKind::kTri1);
  EXPECT_EQ(items[8]->data_type.kind, DataTypeKind::kUwire);
  EXPECT_EQ(items[9]->data_type.kind, DataTypeKind::kWire);
  EXPECT_EQ(items[10]->data_type.kind, DataTypeKind::kWand);
  EXPECT_EQ(items[11]->data_type.kind, DataTypeKind::kWor);
}

// --- net_port_type ---
// [net_type] data_type_or_implicit | nettype_identifier
// | interconnect implicit_data_type
TEST(ParserA221, NetPortTypeWithNetType) {
  auto r = Parse("module m(inout tri [7:0] bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
}

TEST(ParserA221, VarDataTypeWithVar) {
  // var data_type_or_implicit
  auto r = Parse("module m(input var logic d); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
}

// --- signing ---
// signed | unsigned
TEST(ParserA221, SigningSigned) {
  auto r = Parse("module m; logic signed [7:0] x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->data_type.is_signed);
}

// --- simple_type ---
// integer_type | non_integer_type | ps_type_identifier |
// ps_parameter_identifier (covered by casting_type and data_type tests above)
// --- struct_union ---
// struct | union [soft | tagged]
TEST(ParserA221, StructUnionStruct) {
  auto r = Parse(
      "module m;\n"
      "  struct { int a; int b; } s;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kStruct);
}

}  // namespace
