#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CastCompatibleParsing, RealToIntCompatible) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleParsing, EnumToIntCompatible) {
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleParsing, IntToEnumCompatible) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  DataType b;
  b.kind = DataTypeKind::kEnum;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleParsing, RealToShortrealCompatible) {
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kShortreal;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleParsing, StringToIntNotCompatible) {
  DataType a;
  a.kind = DataTypeKind::kString;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_FALSE(IsCastCompatible(a, b));
}

TEST(CastCompatibleParsing, AssignmentCompatibleImpliesCastCompatible) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleParsing, EquivalentImpliesCastCompatible) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kReg;
  EXPECT_TRUE(TypesEquivalent(a, b));
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleParsing, IntEnumCastSymmetric) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kEnum;
  EXPECT_TRUE(IsCastCompatible(a, b));
  EXPECT_TRUE(IsCastCompatible(b, a));
}

TEST(CastCompatibleParsing, LogicToEnumCastCompatible) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kEnum;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

}  // namespace
