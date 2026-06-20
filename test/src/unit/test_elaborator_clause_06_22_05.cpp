#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TypeIncompatibleElaboration, StringToIntRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  string s;\n"
      "  int i;\n"
      "  initial i = s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// Claim 1: type-incompatible is the residual — nonequivalent types with no
// implicit or explicit casting rule. A string and an int have neither.
TEST(TypeIncompatibleElaboration, ResidualTypesWithNoCastRuleAreIncompatible) {
  DataType s;
  s.kind = DataTypeKind::kString;
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  ASSERT_FALSE(IsCastCompatible(s, i));
  EXPECT_TRUE(IsTypeIncompatible(s, i));
}

// Claim 1: equivalent types are cast-compatible, hence never incompatible.
TEST(TypeIncompatibleElaboration, EquivalentTypesAreNotIncompatible) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kReg;
  ASSERT_TRUE(TypesEquivalent(a, b));
  EXPECT_FALSE(IsTypeIncompatible(a, b));
}

// Claim 1: nonequivalent integrals carry an implicit cast rule, so they are
// cast-compatible and therefore not type-incompatible.
TEST(TypeIncompatibleElaboration, CastCompatibleTypesAreNotIncompatible) {
  DataType byte_t;
  byte_t.kind = DataTypeKind::kByte;
  byte_t.is_signed = true;
  DataType long_t;
  long_t.kind = DataTypeKind::kLongint;
  long_t.is_signed = true;
  ASSERT_FALSE(TypesEquivalent(byte_t, long_t));
  ASSERT_TRUE(IsCastCompatible(byte_t, long_t));
  EXPECT_FALSE(IsTypeIncompatible(byte_t, long_t));
}

// Claim 2: a chandle is type-incompatible with every other type.
TEST(TypeIncompatibleElaboration, ChandleIsIncompatibleWithOtherTypes) {
  DataType ch;
  ch.kind = DataTypeKind::kChandle;
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  EXPECT_TRUE(IsTypeIncompatible(ch, i));
  EXPECT_TRUE(IsTypeIncompatible(i, ch));

  DataType str;
  str.kind = DataTypeKind::kString;
  EXPECT_TRUE(IsTypeIncompatible(ch, str));
}

// Claim 2: the rule excludes the same handle type — a chandle is compatible
// with another chandle, so it is incompatible only with all *other* types.
TEST(TypeIncompatibleElaboration, ChandleIsCompatibleWithItself) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kChandle;
  EXPECT_FALSE(IsTypeIncompatible(a, b));
}

// Claim 1: the residual excludes types bridged by an *explicit* cast rule too,
// not only implicit ones. An int requires an explicit cast to an enum, so the
// two are cast-compatible and therefore not type-incompatible in either
// direction.
TEST(TypeIncompatibleElaboration, EnumAndIntegralAreNotIncompatible) {
  DataType enum_t;
  enum_t.kind = DataTypeKind::kEnum;
  DataType int_t;
  int_t.kind = DataTypeKind::kInt;
  int_t.is_signed = true;
  ASSERT_TRUE(IsCastCompatible(int_t, enum_t));
  EXPECT_FALSE(IsTypeIncompatible(enum_t, int_t));
  EXPECT_FALSE(IsTypeIncompatible(int_t, enum_t));
}

// Claim 2: a class handle is written as a named type; it is type-incompatible
// with every type other than the same named handle (the residual rule).
TEST(TypeIncompatibleElaboration, ClassHandleIncompatibleWithOtherTypes) {
  DataType handle;
  handle.kind = DataTypeKind::kNamed;
  handle.type_name = "my_class";
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  EXPECT_TRUE(IsTypeIncompatible(handle, i));

  DataType other;
  other.kind = DataTypeKind::kNamed;
  other.type_name = "other_class";
  EXPECT_TRUE(IsTypeIncompatible(handle, other));

  DataType same;
  same.kind = DataTypeKind::kNamed;
  same.type_name = "my_class";
  EXPECT_FALSE(IsTypeIncompatible(handle, same));
}

}  // namespace
