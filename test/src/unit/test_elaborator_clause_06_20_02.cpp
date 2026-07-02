#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ValueParameters, RealParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter real r = 5.7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters, ModuleWithTypedParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameters, MultipleParamsResolveCorrectValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter e = 25, f = 9;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "e");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 25);
  EXPECT_EQ(design->top_modules[0]->params[1].name, "f");
  EXPECT_EQ(design->top_modules[0]->params[1].resolved_value, 9);
}

TEST(ValueParameters, ParameterRefResolvesValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = 5;\n"
      "  parameter int B = A;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_TRUE(b.is_resolved);
  EXPECT_EQ(b.resolved_value, 5);
}

TEST(ValueParameters, DependentParamResolvesValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  parameter int MASK = (1 << WIDTH) - 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& mask = design->top_modules[0]->params[1];
  EXPECT_EQ(mask.name, "MASK");
  EXPECT_TRUE(mask.is_resolved);
  EXPECT_EQ(mask.resolved_value, 255);
}

// §6.20.2: a parameter with neither a type nor a range specification takes its
// type and range from the value assigned to it; nothing is fixed by the
// declaration itself.
TEST(ValueParameters, UntypedUnrangedHasNoDeclaredTypeOrRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_FALSE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.resolved_value, 42);
}

// §6.20.2: a parameter with a range but no type specification has the range of
// its declaration and is unsigned.
TEST(ValueParameters, RangedUntypedIsUnsignedWithDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [7:0] P = 200;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_range);
  EXPECT_FALSE(p.has_decl_type);
  EXPECT_FALSE(p.decl_is_signed);
  EXPECT_EQ(p.decl_width, 8u);
}

// §6.20.2: a parameter with a type but no range specification is of the type
// specified; an int parameter carries that type's 32-bit width.
TEST(ValueParameters, TypedUnrangedTakesDeclaredType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 32u);
}

// §6.20.2: a parameter with a signed type specification and a range is signed
// and has the range of its declaration.
TEST(ValueParameters, SignedRangedIsSignedWithDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter signed [3:0] s = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_TRUE(p.has_decl_range);
  EXPECT_TRUE(p.decl_is_signed);
  EXPECT_EQ(p.decl_width, 4u);
}

// §6.20.2: the sign and range of a ranged, untyped parameter are not affected
// by a value override, so an override is coerced into the declared (unsigned)
// width.
TEST(ValueParameters, OverrideDoesNotAffectUnsignedRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter [3:0] P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(255) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].name, "P");
  EXPECT_EQ(child->params[0].resolved_value, 15);
}

// §6.20.2: a signed, ranged parameter keeps its sign and range under an
// override, so the override is coerced to the declared width with sign
// extension.
TEST(ValueParameters, OverrideDoesNotAffectSignedRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter signed [3:0] P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(8)) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].resolved_value, -8);
}

// §6.20.2: a parameter with no range and only an implicit (bare `signed`) type
// takes its range from the final value, so an override is not masked to a
// fixed declared width.
TEST(ValueParameters, OverrideOnSignedImplicitFollowsValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter signed P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(5)) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].resolved_value, 5);
}

// §6.20.2: bit-selects and part-selects of a parameter of an integral type are
// allowed; here a part-select of an integral parameter feeds another
// parameter's constant value.
TEST(ValueParameters, PartSelectOfIntegralParameterAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam [7:0] P = 8'hAB;\n"
      "  localparam X = P[3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& x = design->top_modules[0]->params[1];
  EXPECT_EQ(x.name, "X");
  EXPECT_TRUE(x.is_resolved);
  EXPECT_EQ(x.resolved_value, 0xB);
}

// §6.20.2: a single-bit select of an integral parameter is likewise allowed;
// bit 7 of 8'hAB is 1.
TEST(ValueParameters, BitSelectOfIntegralParameterAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam [7:0] P = 8'hAB;\n"
      "  localparam B = P[7];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_TRUE(b.is_resolved);
  EXPECT_EQ(b.resolved_value, 1);
}

// §6.20.2: a value parameter may be set to an expression built from another
// local parameter, one of the allowed constant primaries.
TEST(ValueParameters, LocalParamSetFromLocalParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam A = 5;\n"
      "  localparam B = A;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_TRUE(b.is_resolved);
  EXPECT_EQ(b.resolved_value, 5);
}

// §6.20.2: a parameter with a concrete data type but no range takes that
// type's width; a byte parameter is 8 bits wide.
TEST(ValueParameters, ByteTypedParameterTakesByteWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter byte W = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 8u);
}

// §6.20.2: the sign and range of a signed, ranged parameter are fixed by its
// declaration, so a negative override survives unchanged when it fits the
// declared width.
TEST(ValueParameters, SignedOverrideRoundTripsNegative) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter signed [3:0] P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(-2)) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].resolved_value, -2);
}

// §6.20.2: the real-to-integer conversion of §6.12.1 applies to parameters, so
// an integer-typed parameter initialized from a real constant rounds to the
// nearest integer (5.7 -> 6).
TEST(ValueParameters, IntegerParameterFromRealConstantRounds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = 5.7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "W");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 6);
}

// §6.20.2: the §6.12.1 real-to-integer conversion applies whenever the
// parameter is in an integer context. A parameter with a packed range but no
// type keyword is in an integer context by virtue of the range alone, so a real
// initializer is rounded to the nearest integer (5.7 -> 6). This exercises the
// range-induced integer context, distinct from the type-induced context of the
// `int`/`integer` tests above. Rounding (6) rather than truncation (5) confirms
// the §6.12.1 rule and not a mere cast.
TEST(ValueParameters, RangedUntypedParameterAppliesRealToIntConversion) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [7:0] P = 5.7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.has_decl_range);
  EXPECT_FALSE(p.has_decl_type);
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 6);
}

// §6.20.2: the same conversion rounds half away from zero for negative real
// initializers (-2.5 -> -3) of an integer-typed parameter.
TEST(ValueParameters, IntegerParameterFromNegativeRealRoundsAwayFromZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter integer N = -2.5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "N");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, -3);
}

// §6.20.2 (R3): "a parameter with a type but no range is of the type
// specified." The rule must adapt to each admitted integer type, so a shortint
// parameter carries that type's 16-bit width. Input form distinct from the
// int/byte tests: a different concrete two-state type.
TEST(ValueParameters, ShortintTypedParameterTakesShortintWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter shortint W = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 16u);
}

// §6.20.2 (R3): a longint parameter is of the longint type and so carries its
// 64-bit width — the widest admitted integer type input form.
TEST(ValueParameters, LongintTypedParameterTakesLongintWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter longint W = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 64u);
}

// §6.20.2 (R3): a bit-typed parameter is of the single-bit `bit` type, the
// narrowest admitted type input form (width 1).
TEST(ValueParameters, BitTypedParameterTakesSingleBitWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter bit B = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_TRUE(p.has_decl_type);
  EXPECT_FALSE(p.has_decl_range);
  EXPECT_EQ(p.decl_width, 1u);
}

// §6.20.2 (R2): a ranged, untyped parameter "shall be unsigned" and its range
// is not affected by an override. A negative override value therefore does not
// make the parameter signed: -1 into a 4-bit unsigned parameter is coerced to
// its unsigned representation (15), not left as -1. This is the
// negative-override input form, complementing the large-positive override test
// above.
TEST(ValueParameters, NegativeOverrideIntoUnsignedRangeBecomesUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter [3:0] P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(-1) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].resolved_value, 15);
}

// §6.20.2 (R8, via §6.12.1): a real initializer exactly on a half boundary
// rounds away from zero. Positive-tie input form: 2.5 -> 3 (a plain cast would
// truncate to 2, and round-to-even would give 2), complementing the negative
// tie -2.5 -> -3.
TEST(ValueParameters, IntegerParameterFromPositiveHalfRoundsAwayFromZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = 2.5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "W");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 3);
}

// §6.20.2 (R9): bit-/part-selects of parameters of integral types are allowed.
// Integral-operand input form distinct from the packed-range declaration: here
// the parameter is declared with the integral type `int`, and a part-select of
// it still folds to a constant (bits [3:0] of 0xAB == 0xB).
TEST(ValueParameters, PartSelectOfIntegerTypedParameterAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int P = 8'hAB;\n"
      "  localparam B = P[3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_TRUE(b.is_resolved);
  EXPECT_EQ(b.resolved_value, 0xB);
}

// §6.20.2 (R9, negative): the rule permits selects only of parameters of
// integral types. A real parameter is not integral, so a bit-select of it is
// not allowed; here a continuous assignment reads bit 0 of a real parameter and
// the elaborator rejects it. Built from real value-parameter syntax and driven
// through the full parse+elaborate pipeline.
TEST(ValueParameters, BitSelectOfRealParameterRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter real R = 1.5;\n"
      "  logic x;\n"
      "  assign x = R[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
