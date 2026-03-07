#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection6, AssignmentCompatibleRealToReal) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kShortreal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignCompatibleByteToShortint) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignCompatibleRealToReal) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kReal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignCompatibleEnumToLogic) {
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignmentCompatibleIntegral) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignmentCompatibleEnumToInt) {
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, NotAssignmentCompatibleStringInt) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsAssignmentCompatible(a, b));
}

// §6.22.3: Real types are assignment compatible with integral types.
TEST(ParserSection6, AssignCompatibleRealToLogic) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

// §6.22.3: Realtime and shortreal are assignment compatible.
TEST(ParserSection6, AssignCompatibleRealtimeToShortreal) {
  DataType a;
  a.kind = DataTypeKind::kRealtime;
  DataType b;
  b.kind = DataTypeKind::kShortreal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

// §6.22.3: Chandle is not assignment compatible with integral.
TEST(ParserSection6, NotAssignCompatibleChandleToInt) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsAssignmentCompatible(a, b));
}

}  // namespace
