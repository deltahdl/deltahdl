#include "fixture_elaborator.h"

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
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  const RtlirVariable* data = nullptr;
  for (const auto& v : u0->variables) {
    if (v.name == "data") data = &v;
  }
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 32u);
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
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  const RtlirVariable* data = nullptr;
  for (const auto& v : u0->variables) {
    if (v.name == "data") data = &v;
  }
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 32u);
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
