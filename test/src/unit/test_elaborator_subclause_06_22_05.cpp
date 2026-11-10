#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
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

constexpr std::string_view kHandleTypes =
    "  class K; endclass\n"
    "  interface class IC; endclass\n"
    "  class KI implements IC; endclass\n"
    "  K k; IC ic; KI ki; chandle ch; int i; string s; event ev;\n";

std::string HandleModule(std::string_view stmt) {
  return "module t;\n" + std::string(kHandleTypes) + "  initial " +
         std::string(stmt) + "\nendmodule\n";
}

struct IncompatibleWrite {
  std::string_view stmt;
  std::string_view report;
  std::string_view subclause;
};

constexpr IncompatibleWrite kReportedIncompatibleWrites[] = {
    {"i = k;", "cannot assign class object handle to a non-class variable",
     "8.4"},
    {"s = k;", "cannot assign class object handle to a non-class variable",
     "8.4"},
    {"i = ic;", "cannot assign class object handle to a non-class variable",
     "8.4"},
    {"i = int'(k);", "cannot cast class object handle to a non-class type",
     "8.4"},
    {"k = K'(i);", "cannot cast non-class value to a class type", "8.4"},
    {"ch = i;", "chandle can only be assigned from another chandle or null",
     "6.14"},
    {"i = ch;", "chandle cannot be assigned to a non-chandle variable", "6.14"},
    {"s = ch;", "chandle cannot be assigned to a non-chandle variable", "6.14"},
    {"k = ch;", "chandle cannot be assigned to a non-chandle variable", "6.14"},
    {"ic = ch;", "chandle cannot be assigned to a non-chandle variable",
     "6.14"},
};

TEST(TypeIncompatibleElaboration, HandleWritesAcrossTypesAreReported) {
  for (const auto& write : kReportedIncompatibleWrites) {
    std::string src = HandleModule(write.stmt);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string(write.report),
                              LineHolding(src, write.stmt),
                              std::string(write.subclause)));
  }
}

TEST(TypeIncompatibleElaboration,
     DISABLED_NonClassVariableWrittenToAHandleIsReported) {
  for (std::string_view stmt : {"k = i;", "ic = i;", "k = ev;"}) {
    std::string src = HandleModule(stmt);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "cannot assign non-class value to class object handle",
                      LineHolding(src, stmt), "8.4"));
  }
}

TEST(TypeIncompatibleElaboration, DISABLED_ChandleCastToAnIntIsReported) {
  std::string src = HandleModule("i = int'(ch);");
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "chandle",
                            LineHolding(src, "int'(ch)"), "6.14"));
}

TEST(TypeIncompatibleElaboration, HandlesOfTheirOwnKindAndNullAreAccepted) {
  ElabFixture f;
  ElaborateSrc(HandleModule("begin ic = ki; ic = null; k = null; ch = null; "
                            "k = new; end"),
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
