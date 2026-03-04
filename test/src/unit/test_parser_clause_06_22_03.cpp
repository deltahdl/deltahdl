// §6.22.3: Assignment compatible

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

// =========================================================================
// §6.22.2: Type compatibility rules — packed width comparison
// =========================================================================
TEST(ParserSection6, AssignCompatibleByteToShortint) {
  // §6.22.2: byte (8-bit 2-state) and shortint (16-bit 2-state) differ
  // in width, but both are integral so assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kByte;
  DataType b;
  b.kind = DataTypeKind::kShortint;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

// =========================================================================
// §6.22.3: Type assignment compatibility
// =========================================================================
TEST(ParserSection6, AssignCompatibleRealToReal) {
  // §6.22.3: real to real is assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kReal;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignCompatibleEnumToLogic) {
  // §6.22.3: enum base type is integral, so enum to integral is compatible.
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignmentCompatibleIntegral) {
  // §6.22.3: All integral types are assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, AssignmentCompatibleEnumToInt) {
  // §6.22.3: enum → integral is assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

TEST(ParserSection6, NotAssignmentCompatibleStringInt) {
  // string and int are not assignment compatible.
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsAssignmentCompatible(a, b));
}

}  // namespace
