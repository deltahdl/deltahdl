#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PrimaryElaboration, RealParameter) {
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

// §6.20.2: the declared range is not widened by an override, so an unsigned
// override that exceeds the declared width is reduced to that width (16 in a
// 4-bit parameter wraps to 0).
TEST(ValueParameters, UnsignedOverrideWrapsToDeclaredWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter [3:0] P = 0);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(16) u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->children.size(), 1u);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_GE(child->params.size(), 1u);
  EXPECT_EQ(child->params[0].resolved_value, 0);
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

}  // namespace
