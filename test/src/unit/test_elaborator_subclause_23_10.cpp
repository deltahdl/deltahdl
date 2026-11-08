#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_child_instance.h"
#include "helpers_reported_error.h"

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

TEST(ParameterOverride,
     BareClassSpecializationOverrideSuppliesTheClassParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class D #(int p);\n"
      "  int data;\n"
      "endclass\n"
      "module child #(parameter type P = int)();\n"
      "  P obj;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(D#(4))) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParameterOverride, BareClassNameOverrideHasNoDefaultSpecialization) {
  ElabFixture f;
  ElaborateSrc(
      "class D #(int p);\n"
      "  int data;\n"
      "endclass\n"
      "module child #(parameter type P = int)();\n"
      "  P obj;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(D)) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "has no default specialization; parameter", 5,
                            "8.25"));
}

TEST(ParameterOverride, BareClassSpecializationOverrideCarriesItsArgument) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class my_obj;\n"
      "endclass\n"
      "module child #(parameter type P = int)();\n"
      "  P wr;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(weak_reference#(my_obj))) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParameterOverride,
     BareClassSpecializationOverrideRejectsANonClassArgument) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter type P = int)();\n"
      "  P wr;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(weak_reference#(int))) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "weak_reference needs a class type as its type parameter", 2, "8.30.1"));
}

TEST(ParameterOverride,
     TypeParameterOverriddenByClassSpecializationWithNamedArgument) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Buf #(type T1 = int, type T2 = bit);\n"
      "  typedef T2 elem_t;\n"
      "endclass\n"
      "module child #(parameter type P = longint)();\n"
      "  P data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(Buf#(.T2(byte))::elem_t)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "data", 8u);
}

TEST(ParameterOverride,
     NamedSpecializationArgumentNamingNoClassParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class Buf #(type T1 = int, type T2 = bit);\n"
      "  typedef T2 elem_t;\n"
      "endclass\n"
      "module child #(parameter type P = longint)();\n"
      "  P data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(Buf#(.Nope(byte))::elem_t)) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'Buf' has no parameter 'Nope'", 8,
                            "23.10.2.2"));
}

TEST(ParameterOverride,
     TypeParameterOverriddenBySignedIntegerTypeInASpecialization) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Buf #(type T1 = int, type T2 = int);\n"
      "  typedef T2 elem_t;\n"
      "endclass\n"
      "module child #(parameter type T = byte)();\n"
      "  T data;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(Buf#(.T2(int unsigned))::elem_t)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* child = SoleChildInstance(design);
  ASSERT_NE(child, nullptr);
  const RtlirVariable* data = nullptr;
  for (const auto& v : child->variables) {
    if (v.name == "data") data = &v;
  }
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data->width, 32u);
  EXPECT_FALSE(data->is_signed);
}

}  // namespace
