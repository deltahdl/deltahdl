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

// §6.19: "Hierarchical names and const variables are not allowed."
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

// §6.19: "If the first name is not assigned a value, it is given the initial
// value of 0." + "A name without a value is automatically assigned an
// increment of the value of the previous name."
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

// §6.19 + §6.20: "...can include references to parameters, local parameters,
// genvars, other enum named constants, and constant functions of these."
// Sanity that a parameter reference is still accepted as the spec intends.
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

// §6.19 footnote 19: "A type_identifier shall be legal as an
// enum_base_type if it denotes an integer_atom_type ... or an
// integer_vector_type." A typedef of a struct (a non-integer type) used as
// the enum base shall be rejected by the elaborator.
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

// §6.19: "An enum declaration of a 4-state type, such as integer, that
// includes one or more names with x or z assignments shall be permitted."
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

}  // namespace
