#include <gtest/gtest.h>


#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

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
  // Both named constants are 4 bits wide against a 3-bit base, so the report
  // stands twice; the first is on the line of Global's value.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "enum literal width 4 does not match base type "
                            "width 3",
                            3, "6.19"));
}

TEST(EnumerationElaboration, EnumXZin2State_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum bit [1:0] {a=0, b=2'bxx, c=1} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "x/z value in 2-state enum is illegal", 2, "6.19"));
}

TEST(EnumerationElaboration, EnumUnassignedAfterXZ_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum integer {a=0, b={32{1'bx}}, c} val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unassigned enum member 'c' follows member with "
                            "x/z value",
                            2, "6.19"));
}

TEST(EnumerationElaboration, EnumDuplicateValue_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  enum {a=0, b=7, c, d=8} x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate enum member value 8", 2, "6.19"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate enum member name 'A'", 2, "6.19"));
}

TEST(EnumerationElaboration, EnumAutoIncrementOverflow_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit [0:0] {A, B, C} x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "enum auto-increment exceeds maximum representable "
                            "value of base type",
                            2, "6.19"));
}

TEST(EnumerationElaboration, EnumHierarchicalNameInitializer_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter int X = 1;\n"
      "  enum integer {A = top.X, B} v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name not allowed in enum named "
                            "constant value",
                            3, "6.19"));
}

TEST(EnumerationElaboration, EnumConstVariableInitializer_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int K = 7;\n"
      "  enum integer {A = K, B} v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "const variable 'K' not allowed in enum named "
                            "constant value",
                            3, "6.19"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "enum base type 'pair_t' is not an "
                            "integer_atom_type or integer_vector_type",
                            3, "6.19"));
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

// §6.19: one enumeration declaration declares its set of named constants once,
// and the clause's own `enum {red, yellow, green} light1, light2;` gives that
// one set to both declarators. The names are not redeclared by the second name
// in the list, so this is legal where two separate declarations of red would
// not be (see EnumMemberNameReusedInSameScope_Error).
TEST(EnumerationElaboration, EnumSharedByTwoDeclaratorsDeclaresItsNamesOnce) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  enum {red, yellow, green} light1, light2;\n"
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
  // medal2 declares the three names, so the clash is reported against medal3
  // on line 3, once per name; the assertion names the first of the three.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "enum member name 'bronze' is already declared in "
                            "this scope",
                            3, "6.19"));
}

TEST(EnumerationElaboration, EnumAtomTypeBaseWithPackedDim_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef int my_int_t;\n"
      "  enum my_int_t [3:0] {A, B, C} state;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension not permitted on enum base type "
                            "'my_int_t' that denotes an integer_atom_type",
                            3, "6.19"));
}

TEST(EnumerationElaboration, EnumUnsignedValueOutsideRange_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit [3:0] {a = 'h10} m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "enum member 'a' value 16 is outside the "
                            "representable range of the base type",
                            2, "6.19"));
}

TEST(EnumerationElaboration, EnumSignedValueOutsideRange_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit signed [3:0] {a = 200} m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "enum member 'a' value 200 is outside the "
                            "representable range of the base type",
                            2, "6.19"));
}

TEST(EnumerationElaboration, EnumSignedValueBelowMin_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit signed [3:0] {a = -100} m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "enum member 'a' value -100 is outside the "
                            "representable range of the base type",
                            2, "6.19"));
}

TEST(EnumerationElaboration, EnumUnsignedNegativeValue_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  enum bit [3:0] {a = -1} m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "enum member 'a' value -1 is outside the "
                            "representable range of the base type",
                            2, "6.19"));
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

// §6.19 (printed page 119) has an enumerated type declare its literals as
// named constants, and printed 120 makes two enumerations naming one literal
// illegal in one scope, so the literals stand in the scope holding the enum;
// §7.2's Syntax 7-1 (printed 146) gives a structure member any data_type, the
// enum form among them, and §23.9's list of the elements that define a scope
// (printed 761) names no structure, so IDLE and BUSY are constants of p, read
// through §26.3's package scope resolution operator into a localparam. K folds
// to 1 * 10 + 0 = 10; a package that recorded neither constant left K
// unresolved, the "p.BUSY" fold of RegisterPackageParams reading the members
// of an enumeration written at the top of a typedef alone.
TEST(EnumerationElaboration,
     StructMemberEnumLiteralOfAPackageFoldsIntoALocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef struct { enum {IDLE, BUSY} st; int n; } s_t;\n"
      "endpackage\n"
      "module top;\n"
      "  localparam int K = p::BUSY * 10 + p::IDLE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* param = FindParam(design, "top", "K");
  ASSERT_NE(param, nullptr);
  EXPECT_TRUE(param->is_resolved);
  EXPECT_EQ(param->resolved_value, 10);
}

// The same clauses for a module's own typedef: the member's enumeration
// declares A and B in the module, and each enumeration numbers its literals
// from 0 on its own (printed 120), so the second member's C is 0 again and
// D 1, not a continuation of the first. K folds to 1 * 100 + 0 * 10 + 1 =
// 101; before, ElaborateTypedef declared the constants of a typedef naming
// the enum form alone, and `B` was reported an unresolved identifier.
TEST(EnumerationElaboration,
     StructMemberEnumLiteralOfAModuleFoldsIntoALocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct { enum {A, B} e; enum {C, D} g; int n; } t;\n"
      "  localparam int K = B * 100 + C * 10 + D;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* param = FindParam(design, "top", "K");
  ASSERT_NE(param, nullptr);
  EXPECT_TRUE(param->is_resolved);
  EXPECT_EQ(param->resolved_value, 101);
}

// §7.2 (printed 146) gives struct_union_member to a union as to a structure,
// and a member's value may be written (printed 120): a union member's
// enumeration with `HI = 5` declares LO as 4 in the module, so K folds to
// 5 * 10 + 4 = 54, and a data declaration of the union type declares the
// constants a second time no more than `light1, light2` does. An enumeration
// written on a union's member declared nothing before.
TEST(EnumerationElaboration, UnionMemberEnumLiteralFoldsIntoALocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef union { enum {LO = 4, HI} tag; int n; } u_t;\n"
      "  u_t u;\n"
      "  localparam int K = HI * 10 + LO;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* param = FindParam(design, "top", "K");
  ASSERT_NE(param, nullptr);
  EXPECT_TRUE(param->is_resolved);
  EXPECT_EQ(param->resolved_value, 54);
}

}  // namespace
