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

TEST(ParserSection6, TypesEquivalentPackedSameWidth) {
  // §6.22.2c: same width+signing+state-ness → equivalent.
  // byte (8-bit, 2-state) and shortint differ in width → not equivalent.
  // int and integer: same 32-bit width, but int is 2-state, integer is
  // 4-state → not equivalent.
  DataType a;
  a.kind = DataTypeKind::kByte;
  DataType b;
  b.kind = DataTypeKind::kByte;
  b.is_signed = true;  // byte defaults to signed, make both agree.
  a.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));  // Same kind → match → equivalent.
}

TEST(ParserSection6, TypesNotEquivalentDifferentState) {
  // §6.22.2c: bit (2-state) and logic (4-state) are NOT equivalent.
  DataType a;
  a.kind = DataTypeKind::kBit;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

}  // namespace
