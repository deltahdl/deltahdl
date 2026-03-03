// §6.22.1: Matching types

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypeCompatibilityAnonymousStruct) {
  // §6.22.1c: Anonymous struct matches itself within same declaration.
  auto r = Parse(
      "module m;\n"
      "  struct packed { int A; int B; } AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // AB1 and AB2 should both be declared
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesSameSigningModifier) {
  // §6.22.1g: Explicitly adding signed to a type that is already signed
  // creates a matching type.
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kByte;
  b.is_signed = true;
  EXPECT_TRUE(TypesMatch(a, b));
}

// =========================================================================
// §6.22: Type compatibility — TypesMatch on named types
// =========================================================================
TEST(ParserSection6, TypesMatchNamedSameType) {
  // §6.22: Two kNamed types with the same type_name match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "mytype";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "mytype";
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchNamedDifferentType) {
  // §6.22: Two kNamed types with different type_names do not match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "type_a";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "type_b";
  EXPECT_FALSE(TypesMatch(a, b));
}

// =========================================================================
// §6.22.1: Type equivalence — matching built-in types
// =========================================================================
TEST(ParserSection6, TypesEquivalentSameSignedInt) {
  // §6.22.1/2: Two int types (both signed by default) are equivalent.
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

// =========================================================================
// §6.22: Type compatibility
// =========================================================================
TEST(ParserSection6, TypesMatchBuiltin) {
  // Two identical built-in types should match.
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
  // Same kind but different signedness should not match.
  DataType a;
  a.kind = DataTypeKind::kLogic;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  b.is_signed = false;
  EXPECT_FALSE(TypesMatch(a, b));
}

}  // namespace
