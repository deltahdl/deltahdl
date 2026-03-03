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

}  // namespace
