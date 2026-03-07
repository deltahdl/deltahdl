#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection6, TypesNotEquivalentDifferentSign) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = false;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(ParserSection6, TypesEquivalentDiffSignedness) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = false;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(ParserSection6, NotEquivalentDiffWidth) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  b.is_signed = true;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(ParserSection6, TypesEquivalentPackedSameWidth) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  DataType b;
  b.kind = DataTypeKind::kByte;
  b.is_signed = true;
  a.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

TEST(ParserSection6, TypesNotEquivalentDifferentState) {
  DataType a;
  a.kind = DataTypeKind::kBit;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(ParserSection6, TypesEquivalentSameKind) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

// §6.22.2: Equivalent types — matching types are always equivalent.
TEST(ParserSection6, EquivalentMatchingImpliesEquivalent) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesMatch(a, b));
  EXPECT_TRUE(TypesEquivalent(a, b));
}

// §6.22.2: Non-integral types are not equivalent to integral types.
TEST(ParserSection6, NotEquivalentStringToInt) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

}  // namespace
