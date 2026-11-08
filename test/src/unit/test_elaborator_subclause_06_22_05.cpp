#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(TypeIncompatibleElaboration, ResidualTypesWithNoCastRuleAreIncompatible) {
  DataType s;
  s.kind = DataTypeKind::kString;
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  ASSERT_FALSE(IsCastCompatible(s, i));
  EXPECT_TRUE(IsTypeIncompatible(s, i));
}

TEST(TypeIncompatibleElaboration, EquivalentTypesAreNotIncompatible) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kReg;
  ASSERT_TRUE(TypesEquivalent(a, b));
  EXPECT_FALSE(IsTypeIncompatible(a, b));
}

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

TEST(TypeIncompatibleElaboration, ChandleIsCompatibleWithItself) {
  DataType a;
  a.kind = DataTypeKind::kChandle;
  DataType b;
  b.kind = DataTypeKind::kChandle;
  EXPECT_FALSE(IsTypeIncompatible(a, b));
}

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
