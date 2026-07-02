#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(EnumerationElaboration, EnumSizedLiteralMismatch_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum logic [2:0] {\n"
      "    Global = 4'h2,\n"
      "    Local = 4'h3\n"
      "  } myenum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumXZin2State_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum bit [1:0] {a=0, b=2'bxx, c=1} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumUnassignedAfterXZ_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum integer {a=0, b={32{1'bx}}, c} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumDuplicateValue_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum {a=0, b=7, c, d=8} x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumDefaultWidthInt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  enum {A, B, C} x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "x") {
      EXPECT_EQ(v.width, 32u);
    }
  }
}

TEST(EnumerationElaboration, EnumExplicitBaseWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  enum logic [3:0] {A, B, C} x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumDuplicateName_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum {A, B, A} x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumAutoIncrementOverflow_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit [0:0] {A, B, C} x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumHierarchicalNameInitializer_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int X = 1;\n"
      "  enum integer {A = top.X, B} v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumConstVariableInitializer_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int K = 7;\n"
      "  enum integer {A = K, B} v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumAutoIncrementValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {A, B=5, C} color_t;\n"
      "  color_t x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("color_t");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "A");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "B");
  EXPECT_EQ(it->second[1].value, 5);
  EXPECT_EQ(it->second[2].name, "C");
  EXPECT_EQ(it->second[2].value, 6);
}

TEST(EnumerationElaboration, EnumParameterInitializer_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  parameter int X = 3;\n"
      "  enum integer {A = X, B} v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumStructTypedefBaseTypeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { int A; } pair_t;\n"
      "  enum pair_t {A, B, C} state;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumIntegerWithXAssignmentPermitted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  enum integer {IDLE = 0, XX = 'x, S1 = 1, S2 = 2} state;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumMemberNameReusedInSameScope_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit [3:0] {bronze=4'h3, silver, gold=4'h5} medal2;\n"
      "  enum bit [3:0] {bronze=4'h3, silver, gold=4'h5} medal3;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumAtomTypeBaseWithPackedDim_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef int my_int_t;\n"
      "  enum my_int_t [3:0] {A, B, C} state;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumUnsignedValueOutsideRange_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit [3:0] {a = 'h10} m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumSignedValueOutsideRange_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit signed [3:0] {a = 200} m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumSignedValueBelowMin_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit signed [3:0] {a = -100} m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumUnsignedNegativeValue_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit [3:0] {a = -1} m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(EnumerationElaboration, EnumVectorTypedefBaseWithPackedDimAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef logic my_logic_t;\n"
      "  enum my_logic_t [3:0] {A, B, C} state;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.19: an enum named-constant value is an elaboration-time constant
// expression (§6.20) and may reference a localparam, not only a parameter.
TEST(EnumerationElaboration, EnumLocalparamInitializer_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam int X = 4;\n"
      "  enum integer {A = X, B} v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
