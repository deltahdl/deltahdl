#include "fixture_elaborator.h"
#include "helpers_child_instance.h"

using namespace delta;

namespace {

TEST(ParameterOverride, DefparamBeatsInstanceParameterAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.WIDTH(8)) u0();\n"
      "  defparam u0.WIDTH = 16;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 16);
}

TEST(ParameterOverride, DefparamBeatsOrderedInstanceParameterAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter WIDTH = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(8) u0();\n"
      "  defparam u0.WIDTH = 24;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 24);
}

TEST(ParameterOverride, UntypedUnrangedAdoptsOverrideValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter P = 3'h2)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = 1000;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 1000);
}

TEST(ParameterOverride, RangedUntypedTruncatesOverrideToDeclarationRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter [2:0] P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = 13;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
}

TEST(ParameterOverride, TypedUnrangedConvertsOverrideToDeclarationType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = 64'h1_0000_0001;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 1);
}

TEST(ParameterOverride, SignedUnrangedAdoptsOverrideRange) {
  // §23.10: a value parameter with a (signed) type specification but no range
  // specification takes its range from the final override value. The override
  // is therefore not truncated to any declared width, and the parameter stays
  // signed, so a negative override survives intact.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter signed P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = -5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, -5);
}

// §23.10: the two kinds of overridable parameter constants are value parameters
// and type parameters. A type parameter is overridden by an ordered instance
// parameter value assignment; the child's body variable, declared with the type
// parameter's type, adopts the width of the override type (int = 32) rather
// than the declared default (byte = 8).
TEST(ParameterOverride, TypeParameterOverriddenByOrderedInstanceAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(int) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 32u);
}

// §23.10: the same type-parameter override reached by a named instance
// parameter value assignment. Without the override the variable would be 16
// bits wide (shortint), so observing 32 bits confirms the override is applied.
TEST(ParameterOverride, TypeParameterOverriddenByNamedInstanceAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = shortint)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(int)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 32u);
}

// §23.10.2: an instance parameter value assignment overrides a type parameter
// with a type, and §6.18's user-defined type name is one. The override names a
// typedef declared in the instantiating module, so the child's variable is 16
// bits wide (shortint). An override the elaborator does not carry into the
// child leaves the declared default standing, which reads back as 8 (byte).
TEST(ParameterOverride, TypeParameterOverriddenByTypedefNameInNamedAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  typedef shortint word_t;\n"
      "  child #(.T(word_t)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 16u);
}

// §8.23: a type parameter assignment is one of the three contexts in which a
// class may prefix the class scope resolution operator, so the type selected
// out of the class is what the child's type parameter takes. The child's
// variable is therefore 8 bits wide (byte); a dropped override reads back as
// the declared default's 32 (int).
TEST(ParameterOverride,
     TypeParameterOverriddenByClassScopedNameInNamedAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Frame;\n"
      "  typedef byte payload_t;\n"
      "endclass\n"
      "module child #(parameter type T = int)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(Frame::payload_t)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 8u);
}

// §23.10.2: an ordered instance parameter value assignment overrides the same
// type parameter by position rather than by name, and the two forms are matched
// against the child's declaration separately. The §8.23 class-scoped override
// therefore has to reach the child through the ordered form too, giving 8 bits
// (byte) rather than the declared default's 32 (int).
TEST(ParameterOverride,
     TypeParameterOverriddenByClassScopedNameInOrderedAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Frame;\n"
      "  typedef byte payload_t;\n"
      "endclass\n"
      "module child #(parameter type T = int)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(Frame::payload_t) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 8u);
}

// §6.20.3: the value assigned to a type parameter is a data type, and a packed
// vector is a data type that is neither a bare keyword nor a name. The child's
// variable is 16 bits wide; an override understood only when it is a single
// name leaves the declared default standing, which reads back as 8 (byte).
TEST(ParameterOverride,
     TypeParameterOverriddenByPackedVectorInNamedAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(logic [15:0])) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 16u);
}

// §7.4.1 (printed page 153) allows more than one packed dimension on a vector
// type and declares `bit [0:3] [7:0] packedArray;` as its example, so
// `logic [3:0][7:0]` is a data type §6.20.3 lets a type parameter take. Its
// width is the product of the two ranges, 32, which is what separates both
// dimensions reaching the child from only the first doing so: an override
// carrying `[3:0]` alone would read back as 4, and no override at all as 8
// (byte).
TEST(ParameterOverride,
     TypeParameterOverriddenByTwoPackedDimensionsInNamedAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(logic [3:0][7:0])) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 32u);
}

// §6.20.1: a type parameter with no default is an error only when no override
// is supplied at instantiation. A §8.23 class-scoped override supplies one, so
// the instantiation elaborates and the child's variable is 8 bits wide (byte).
// An override dropped before that check is indistinguishable from no override
// at all, and the design is rejected instead.
TEST(ParameterOverride, TypeParameterWithoutDefaultTakesClassScopedOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Frame;\n"
      "  typedef byte payload_t;\n"
      "endclass\n"
      "module child #(parameter type T)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(Frame::payload_t)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 8u);
}

TEST(ParameterOverride, SignedRangedKeepsDeclarationRangeAndSignedness) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter signed [3:0] P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = 17;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 1);
}

// §23.10: the value-parameter type/range override rules apply to a module
// instance parameter value assignment, not only to a defparam. This exercises
// the instantiation-override code path (which coerces the value to the declared
// width) via an ordered assignment on a ranged, untyped parameter: 13 is
// truncated to the declared 3-bit range, giving 5.
TEST(ParameterOverride, RangedUntypedTruncatesOrderedInstanceOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter [2:0] P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(13) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 5);
}

// §23.10: the same override rules reached by a named instance parameter value
// assignment on a typed, unranged parameter. The 33-bit override is converted
// to the parameter's declared 32-bit int type, so only the low bit survives.
TEST(ParameterOverride, TypedUnrangedConvertsNamedInstanceOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P = 0)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(64'h1_0000_0001)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  EXPECT_EQ(u0->params[0].resolved_value, 1);
}

// A type parameter overridden by a package-qualified type name. §26.3 (printed
// page 808) references a package's declarations through the package name, and
// §23.10 makes a type parameter overridable by a data type, so `pkg::word_t` is
// a value this assignment may carry. It is the one override form that reaches
// ResolveNamed in src/elaborator/type_eval.cpp still carrying its prefix:
// ClassScopedOverrideToDataType in src/elaborator/elaborator_module_inst.cpp
// resolves a class-scoped override itself and publishes the resolved type, and
// hands on the unresolved scope_name plus type_name shape only when that lookup
// finds nothing, which a package prefix always does.
//
// 16 is shortint, against the 8 of the byte default the override replaces.
TEST(ParameterOverride, TypeParameterOverriddenByPackageScopedTypeName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef shortint word_t;\n"
      "endpackage\n"
      "module child #(parameter type T = byte)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(pkg::word_t)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 16u);
}

// §8.25 (printed page 204) states that "a generic class is not a type; only a
// concrete specialization represents a type", and that two specializations are
// the same type only when all their parameters are the same. So Buf#(byte) and
// Buf#(shortint) name different types, and the elem_t of the first is a byte.
// The width is read back because an override that dropped the #(byte) would
// still name a type and so would be reported nowhere: the child's variable
// would take the class's own default of int, 32 bits, or the child's declared
// default of longint, 64.
TEST(ParameterOverride,
     TypeParameterOverriddenByClassSpecializationScopedName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Buf #(type T = int);\n"
      "  typedef T elem_t;\n"
      "endclass\n"
      "module child #(parameter type P = longint)();\n"
      "  P data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(Buf#(byte)::elem_t)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 8u);
}

// §23.10.2.1 assigns a parameter by position rather than by name, and
// ResolvePositionalInstParams in src/elaborator/elaborator_module_inst.cpp
// selects the override through a separate path from the named form. The
// specialization has to survive that path too, giving 8 rather than the child's
// declared default of 64.
TEST(ParameterOverride,
     TypeParameterOverriddenByClassSpecializationInOrderedAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Buf #(type T = int);\n"
      "  typedef T elem_t;\n"
      "endclass\n"
      "module child #(parameter type P = longint)();\n"
      "  P data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(Buf#(byte)::elem_t) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 8u);
}

// A second argument to the same class, so that reaching 8 bits above cannot be
// done by reading any one type and calling it the answer. §8.25 (printed page
// 204) makes Buf#(shortint) a distinct type from Buf#(byte), and its elem_t is
// 16 bits.
TEST(ParameterOverride, TypeParameterOverriddenByASecondClassSpecialization) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Buf #(type T = int);\n"
      "  typedef T elem_t;\n"
      "endclass\n"
      "module child #(parameter type P = longint)();\n"
      "  P data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(Buf#(shortint)::elem_t)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 16u);
}

// §8.25.1 (printed page 205) states that "the default specialization of a
// parameterized class is the specialization of the parameterized class with an
// empty parameter override list", and that outside the class the explicit
// specialization form is what a scope resolution shall be written with. So
// Buf#()::elem_t names elem_t with T at the int its declaration gives, 32 bits,
// and neither the child's declared default of 64 nor a failure to name a type.
TEST(ParameterOverride, TypeParameterOverriddenByDefaultClassSpecialization) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Buf #(type T = int);\n"
      "  typedef T elem_t;\n"
      "endclass\n"
      "module child #(parameter type P = longint)();\n"
      "  P data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(Buf#()::elem_t)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 32u);
}

}  // namespace
