#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(EquivalentTypesParsing, TypesNotEquivalentDifferentSign) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = false;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesParsing, TypesNotEquivalentDifferentWidth) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  b.is_signed = true;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesParsing, TypesEquivalentPackedSameWidth) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  DataType b;
  b.kind = DataTypeKind::kByte;
  b.is_signed = true;
  a.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesParsing, TypesNotEquivalentDifferentState) {
  DataType a;
  a.kind = DataTypeKind::kBit;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesParsing, TypesEquivalentSameKind) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesParsing, MatchingTypesImpliesEquivalent) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesMatch(a, b));
  EXPECT_TRUE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesParsing, TypesNotEquivalentStringToInt) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesParsing, IntNotEquivalentToInteger) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInteger;
  b.is_signed = true;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesParsing, LongintNotEquivalentToTime) {
  DataType a;
  a.kind = DataTypeKind::kLongint;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kTime;
  EXPECT_FALSE(TypesEquivalent(a, b));
}

TEST(EquivalentTypesParsing, EquivalentIsSymmetric) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kReg;
  EXPECT_EQ(TypesEquivalent(a, b), TypesEquivalent(b, a));
}

TEST(EquivalentTypesParsing, ElementTypesEquivalentIntAndBitSigned32) {
  EXPECT_TRUE(ElementTypesEquivalent({DataTypeKind::kInt, 32, true, false},
                                     {DataTypeKind::kBit, 32, true, false}));
}

TEST(EquivalentTypesParsing, ElementTypesNotEquivalentDifferentState) {
  EXPECT_FALSE(ElementTypesEquivalent({DataTypeKind::kInt, 32, true, false},
                                      {DataTypeKind::kLogic, 32, false, true}));
}

TEST(EquivalentTypesParsing, ElementTypesNotEquivalentDifferentWidth) {
  EXPECT_FALSE(
      ElementTypesEquivalent({DataTypeKind::kByte, 8, true, false},
                             {DataTypeKind::kShortint, 16, true, false}));
}

TEST(EquivalentTypesParsing, ElementTypesEquivalentLogicAndReg) {
  EXPECT_TRUE(ElementTypesEquivalent({DataTypeKind::kLogic, 8, false, true},
                                     {DataTypeKind::kReg, 8, false, true}));
}

}  // namespace
