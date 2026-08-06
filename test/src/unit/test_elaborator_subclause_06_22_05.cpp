#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.22.5 is a classification rule carried entirely by IsTypeIncompatible: a
// pure, stage-confined predicate over data-type kinds. It is not wired into the
// assignment path (an end-to-end `i = s` rejection is produced by the §6.22.3
// assignment checker, a different function), so the rule this subclause owns is
// observed by calling the predicate directly.

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

// Claim 2: the clause names class handles and interface class handles as two of
// the three type-incompatible handle categories. Both are class handles spelled
// as a named type, and production carries no field distinguishing the two -- a
// variable of either kind is the same kNamed type -- so a single named-handle
// case observes both categories. The residual rule makes such a handle
// incompatible with every type other than the same named handle.
TEST(TypeIncompatibleElaboration, ClassHandleIncompatibleWithOtherTypes) {
  DataType handle;
  handle.kind = DataTypeKind::kNamed;
  handle.type_name = "my_class";
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  EXPECT_TRUE(IsTypeIncompatible(handle, i));
  EXPECT_TRUE(IsTypeIncompatible(i, handle));

  DataType other;
  other.kind = DataTypeKind::kNamed;
  other.type_name = "other_class";
  EXPECT_TRUE(IsTypeIncompatible(handle, other));

  DataType same;
  same.kind = DataTypeKind::kNamed;
  same.type_name = "my_class";
  EXPECT_FALSE(IsTypeIncompatible(handle, same));
}

// Claim 1: an event is a nonequivalent type with no cast rule to an integral
// type, so it falls in the residual bucket and is type-incompatible with int,
// while remaining compatible with itself (the negative form of the residual).
TEST(TypeIncompatibleElaboration, EventResidualIncompatibleWithInt) {
  DataType ev;
  ev.kind = DataTypeKind::kEvent;
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  ASSERT_FALSE(IsCastCompatible(ev, i));
  EXPECT_TRUE(IsTypeIncompatible(ev, i));
  EXPECT_TRUE(IsTypeIncompatible(i, ev));

  DataType ev2;
  ev2.kind = DataTypeKind::kEvent;
  EXPECT_FALSE(IsTypeIncompatible(ev, ev2));
}

}  // namespace
