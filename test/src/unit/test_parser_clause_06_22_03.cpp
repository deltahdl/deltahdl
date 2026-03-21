#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssignmentCompatibleParsing, RealToShortrealCompatible) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kShortreal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, ByteToShortintCompatible) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, RealToRealCompatible) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kReal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, EnumToLogicCompatible) {
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, IntToLogicCompatible) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, EnumToIntCompatible) {
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, StringToIntNotCompatible) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, RealToLogicCompatible) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, RealtimeToShortrealCompatible) {
  DataType a;
  a.kind = DataTypeKind::kRealtime;
  DataType b;
  b.kind = DataTypeKind::kShortreal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, ChandleToIntNotCompatible) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, IntToEnumNotCompatible) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kEnum;
  EXPECT_FALSE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, EquivalentTypesAreCompatible) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kReg;
  EXPECT_TRUE(TypesEquivalent(a, b));
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, IntegralCompatibleIsSymmetric) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
  EXPECT_TRUE(IsAssignmentCompatible(b, a));
}

TEST(AssignmentCompatibleParsing, EventToIntNotCompatible) {
  DataType a;
  a.kind = DataTypeKind::kEvent;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsAssignmentCompatible(a, b));
}

TEST(AssignmentCompatibleParsing, EnumDirectionalityNotSymmetric) {
  DataType e;
  e.kind = DataTypeKind::kEnum;
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  EXPECT_TRUE(IsAssignmentCompatible(e, i));
  EXPECT_FALSE(IsAssignmentCompatible(i, e));
}

}  // namespace
