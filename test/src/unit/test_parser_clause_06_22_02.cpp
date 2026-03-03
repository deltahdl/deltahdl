// §6.22.2: Equivalent types

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

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
  // §6.22.1: Same kind but different signedness is not equivalent.
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = false;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(ParserSection6, NotEquivalentDiffWidth) {
  // §6.22.2: byte (8-bit) and shortint (16-bit) are NOT equivalent.
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  b.is_signed = true;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

}  // namespace
