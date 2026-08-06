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

TEST(CastCompatibleElaboration, RealAndIntegralAreCastCompatible) {
  DataType r;
  r.kind = DataTypeKind::kReal;
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  EXPECT_TRUE(IsCastCompatible(r, i));
  EXPECT_TRUE(IsCastCompatible(i, r));
}

// Two floating types are assignment compatible with each other (and hence
// cast compatible) -- the both-real arm of the definition, distinct from the
// real<->integral arm above.
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

// §6.22.4's own example: an integral requires a cast to be assigned to an
// enum. That means the integral->enum pair is cast compatible yet NOT
// assignment compatible -- exactly the distinction between §6.22.3 and
// §6.22.4. The reverse direction (enum source) is assignment compatible and so
// needs no cast.
TEST(CastCompatibleElaboration,
     IntegralToEnumNeedsCastNotAssignmentCompatible) {
  DataType integral;
  integral.kind = DataTypeKind::kInt;
  integral.is_signed = true;
  DataType enum_t;
  enum_t.kind = DataTypeKind::kEnum;

  // Integral -> enum: cast compatible but not assignment compatible.
  EXPECT_TRUE(IsCastCompatible(integral, enum_t));
  EXPECT_FALSE(IsAssignmentCompatible(integral, enum_t));

  // Enum -> integral: assignment compatible (hence also cast compatible), no
  // cast required.
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

// Full-pipeline negative counterpart to the cast test above: because an
// integral is only cast compatible (not assignment compatible) with an enum,
// an integral-valued expression assigned to an enum with no cast must be
// rejected. The RHS is a binary expression so it is unambiguously integral
// (a bare name could otherwise be an enum member and needs no cast).
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// The reverse direction is assignment compatible, so an enum value flows into
// an integral target with no cast and elaborates cleanly.
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

// The same example in a different syntactic position: an enum variable's
// declaration initializer. An integral initializer with no cast is rejected,
// exercising the module-item initializer path rather than the procedural
// assignment path covered above.
TEST(CastCompatibleElaboration,
     IntegralInitializerForEnumDeclWithoutCastIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c = 3;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The cast form of that same initializer position is accepted: the §6.24 cast
// makes the integral value legal to initialize the enum with.
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
