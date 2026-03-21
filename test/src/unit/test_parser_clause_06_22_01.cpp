#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(MatchingTypesParsing, AnonymousPackedStructSameDecl) {
  auto r = Parse(
      "module m;\n"
      "  struct packed { int A; int B; } AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);

  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(MatchingTypesParsing, MatchingTypesSameSigningModifier) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kByte;
  b.is_signed = true;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, TypesMatchNamedSameType) {
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "mytype";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "mytype";
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, TypesMatchNamedDifferentType) {
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "type_a";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "type_b";
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, TypesEquivalentSameSignedInt) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

TEST(MatchingTypesParsing, TypesMatchBuiltin) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, TypesMatchDifferent) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kReal;
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, TypesMatchSignedness) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  b.is_signed = false;
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, MatchingTypesBuiltinTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit node;\n"
      "  node n1;\n"
      "  bit n2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(MatchingTypesParsing, MatchingTypesAnonymousStruct) {
  auto r = Parse(
      "module m;\n"
      "  struct packed {int A; int B;} AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
}

TEST(MatchingTypesParsing, MatchingTypesNamedTypedefStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {int A; int B;} AB_t;\n"
      "  AB_t x1;\n"
      "  AB_t x2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(MatchingTypesParsing, MatchingTypesSignedBitVector) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit signed [7:0] BYTE;\n"
      "  BYTE b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(MatchingTypesParsing, MatchingTypesArrayTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef byte MEM_BYTES [256];\n"
      "  MEM_BYTES mem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(MatchingTypesParsing, TypesMatchEventToEvent) {
  DataType a;
  a.kind = DataTypeKind::kEvent;
  DataType b;
  b.kind = DataTypeKind::kEvent;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, TypesMatchStringToString) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kString;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, TypesMatchChandleToHandle) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kChandle;
  EXPECT_TRUE(TypesMatch(a, b));
}

// --- Rule (a): built-in types ---

TEST(MatchingTypesParsing, TypesMatchRealToReal) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kReal;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, TypesMatchEnumToEnum) {
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kEnum;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, TypesMatchStructToStruct) {
  DataType a;
  a.kind = DataTypeKind::kStruct;
  DataType b;
  b.kind = DataTypeKind::kStruct;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(MatchingTypesParsing, BuiltinLogicDoesNotMatchBit) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kBit;
  EXPECT_FALSE(TypesMatch(a, b));
}

// --- Rule (c): anonymous enum/union same declaration ---

TEST(MatchingTypesParsing, AnonymousEnumSameDeclParses) {
  auto r = Parse(
      "module m;\n"
      "  enum {RED, GREEN, BLUE} color1, color2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(MatchingTypesParsing, AnonymousUnionSameDeclParses) {
  auto r = Parse(
      "module m;\n"
      "  union packed {int i; logic [31:0] l;} u1, u2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(MatchingTypesParsing, TwoAnonymousStructDifferentDeclsParses) {
  auto r = Parse(
      "module m;\n"
      "  struct packed {int A; int B;} AB1;\n"
      "  struct packed {int A; int B;} AB3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

// --- Rule (d): typedef enum/union ---

TEST(MatchingTypesParsing, TypedefEnumDeclParses) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {A, B, C} abc_t;\n"
      "  abc_t x;\n"
      "  abc_t y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(MatchingTypesParsing, TypedefUnionDeclParses) {
  auto r = Parse(
      "module m;\n"
      "  typedef union packed {int i; logic [31:0] l;} word_t;\n"
      "  word_t a;\n"
      "  word_t b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

// --- Rule (g): explicit signing matching default ---

TEST(MatchingTypesParsing, ByteExplicitSignedMatchesDefault) {
  auto r = Parse(
      "module m;\n"
      "  byte b1;\n"
      "  byte signed b2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->data_type.is_signed, items[1]->data_type.is_signed);
}

TEST(MatchingTypesParsing, ByteExplicitUnsignedChangesDefault) {
  auto r = Parse(
      "module m;\n"
      "  byte b1;\n"
      "  byte unsigned b2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_TRUE(items[0]->data_type.is_signed);
  EXPECT_FALSE(items[1]->data_type.is_signed);
}

TEST(MatchingTypesParsing, LogicExplicitUnsignedMatchesDefault) {
  auto r = Parse(
      "module m;\n"
      "  logic l1;\n"
      "  logic unsigned l2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->data_type.is_signed, items[1]->data_type.is_signed);
}

// --- Rule (h): package typedef matching ---

TEST(MatchingTypesParsing, PackageTypedefImportParses) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef struct packed {int A;} s_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::s_t;\n"
      "  s_t x;\n"
      "  s_t y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
