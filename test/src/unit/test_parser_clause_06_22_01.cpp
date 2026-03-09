#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypeCompatibilityAnonymousStruct) {
  auto r = Parse(
      "module m;\n"
      "  struct packed { int A; int B; } AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);

  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesSameSigningModifier) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kByte;
  b.is_signed = true;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchNamedSameType) {
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "mytype";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "mytype";
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchNamedDifferentType) {
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "type_a";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "type_b";
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesEquivalentSameSignedInt) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

TEST(ParserSection6, TypesMatchBuiltin) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchDifferent) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kReal;
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchSignedness) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  b.is_signed = false;
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, MatchingTypesBuiltinTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit node;\n"
      "  node n1;\n"
      "  bit n2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesAnonymousStruct) {
  auto r = Parse(
      "module m;\n"
      "  struct packed {int A; int B;} AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
}

TEST(ParserSection6, MatchingTypesNamedTypedefStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {int A; int B;} AB_t;\n"
      "  AB_t x1;\n"
      "  AB_t x2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesSignedBitVector) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit signed [7:0] BYTE;\n"
      "  BYTE b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesArrayTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef byte MEM_BYTES [256];\n"
      "  MEM_BYTES mem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, TypesMatchNamedSame) {
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "mytype";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "mytype";
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchNamedDifferent) {
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "type_a";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "type_b";
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchEventToEvent) {
  DataType a;
  a.kind = DataTypeKind::kEvent;
  DataType b;
  b.kind = DataTypeKind::kEvent;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchStringToString) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kString;
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchChandleToHandle) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kChandle;
  EXPECT_TRUE(TypesMatch(a, b));
}

}  // namespace
