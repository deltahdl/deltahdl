#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

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

TEST(CastCompatibleElaboration,
     IntegralAndEnumAreCastCompatibleBothDirections) {
  DataType integral;
  integral.kind = DataTypeKind::kInt;
  integral.is_signed = true;
  DataType enum_t;
  enum_t.kind = DataTypeKind::kEnum;
  EXPECT_TRUE(IsCastCompatible(integral, enum_t));
  EXPECT_TRUE(IsCastCompatible(enum_t, integral));
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

TEST(CastCompatibleElaboration, UnrelatedNonCastableTypesAreNotCastCompatible) {
  DataType s;
  s.kind = DataTypeKind::kString;
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  ASSERT_FALSE(IsAssignmentCompatible(s, i));
  EXPECT_FALSE(IsCastCompatible(s, i));
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

}  // namespace
