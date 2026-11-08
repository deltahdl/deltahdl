#include <gtest/gtest.h>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CastCompatibleElaboration, AssignmentCompatibleImpliesCastCompatible) {
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kLogic;
  ASSERT_TRUE(IsAssignmentCompatible(a, b));
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleElaboration, EquivalentTypesAreCastCompatible) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kReg;
  ASSERT_TRUE(TypesEquivalent(a, b));
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleElaboration, NonequivalentIntegralsAreCastCompatible) {
  DataType a;
  a.kind = DataTypeKind::kByte;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kLongint;
  b.is_signed = true;
  ASSERT_FALSE(TypesEquivalent(a, b));
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(CastCompatibleElaboration, RealAndIntegralAreCastCompatible) {
  DataType r;
  r.kind = DataTypeKind::kReal;
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  EXPECT_TRUE(IsCastCompatible(r, i));
  EXPECT_TRUE(IsCastCompatible(i, r));
}

TEST(CastCompatibleElaboration, RealTypesAreCastCompatible) {
  DataType r;
  r.kind = DataTypeKind::kReal;
  DataType s;
  s.kind = DataTypeKind::kShortreal;
  ASSERT_TRUE(IsAssignmentCompatible(r, s));
  EXPECT_TRUE(IsCastCompatible(r, s));
}

TEST(CastCompatibleElaboration, UnrelatedNonCastableTypesAreNotCastCompatible) {
  DataType s;
  s.kind = DataTypeKind::kString;
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  ASSERT_FALSE(IsAssignmentCompatible(s, i));
  EXPECT_FALSE(IsCastCompatible(s, i));
}

TEST(CastCompatibleElaboration,
     IntegralToEnumNeedsCastNotAssignmentCompatible) {
  DataType integral;
  integral.kind = DataTypeKind::kInt;
  integral.is_signed = true;
  DataType enum_t;
  enum_t.kind = DataTypeKind::kEnum;

  EXPECT_TRUE(IsCastCompatible(integral, enum_t));
  EXPECT_FALSE(IsAssignmentCompatible(integral, enum_t));

  EXPECT_TRUE(IsAssignmentCompatible(enum_t, integral));
  EXPECT_TRUE(IsCastCompatible(enum_t, integral));
}

TEST(CastCompatibleElaboration, CastExpressionBetweenIntAndEnumElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int i;\n"
      "  initial begin\n"
      "    c = color_t'(i);\n"
      "    i = int'(c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CastCompatibleElaboration, IntegralAssignedToEnumWithoutCastIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int i;\n"
      "  initial c = i + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

TEST(CastCompatibleElaboration, EnumAssignedToIntegralWithoutCastIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int i;\n"
      "  initial i = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CastCompatibleElaboration,
     IntegralInitializerForEnumDeclWithoutCastIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c = 3;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 3,
                            "6.19.3"));
}

TEST(CastCompatibleElaboration, CastInitializerForEnumDeclIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c = color_t'(2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
