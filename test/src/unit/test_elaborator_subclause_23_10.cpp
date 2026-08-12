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

}  // namespace
