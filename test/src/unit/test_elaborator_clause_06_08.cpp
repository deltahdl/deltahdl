#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(VarDecl, ConstWithoutInitializerIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(VarDecl, ConstWithInitializerOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  const int MAX = 100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VarDecl, InitializerPreservedInRtlir) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_NE(mod->variables[0].init_expr, nullptr);
}

TEST(VarDecl, RealIsReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real voltage;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_real);
}

TEST(VarDecl, EventIsEvent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event done;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_event);
}

TEST(VarDecl, MultipleVarsInOneStatement) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  // §6.8: each variable_decl_assignment names a simple variable_identifier, so
  // a single declaration of "a, b, c" elaborates to three variables whose
  // stored names are the bare identifiers. The "t.a" hierarchical path name
  // (§23.6) is a separate concept from the declared name and is not what is
  // recorded here.
  EXPECT_EQ(mod->variables[0].name, "a");
  EXPECT_EQ(mod->variables[1].name, "b");
  EXPECT_EQ(mod->variables[2].name, "c");
}

TEST(VarDecl, VarImplicitElaboratesAsLogic) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  var v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_4state);
}

TEST(VarDecl, AutomaticInPackageIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  automatic int x;\n"
      "endpackage\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(VarDecl, StaticInPackageOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  static int x;\n"
      "endpackage\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VarDecl, AutomaticInProceduralBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x = 5;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(VarDecl, StructPackedDimWithoutPackedKeywordIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct { int x; } [3:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(VarDecl, UnionPackedDimWithoutPackedKeywordIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  union { int x; logic [31:0] y; } [3:0] u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(VarDecl, PackedStructWithPackedDimOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } [3:0] s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VarDecl, PackedUnionWithPackedDimOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } [3:0] u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VarDecl, TypeRefInNetDeclWithWireOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire x;\n"
             "  wire type(x) y;\n"
             "endmodule\n"));
}

TEST(VarDecl, TypeRefInVarDeclWithVarOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  var type(x) y;\n"
             "endmodule\n"));
}

TEST(VarDecl, IntegerAtomTypesAreSignedByDefault) {
  // §6.8: only signed types retain the significance of the sign; byte,
  // shortint, int, integer, and longint are signed by default, while vector
  // types (bit/logic/reg) are unsigned unless explicitly declared signed.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  shortint b;\n"
      "  int c;\n"
      "  integer d;\n"
      "  longint e;\n"
      "  bit [7:0] u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 6u);
  EXPECT_TRUE(mod->variables[0].is_signed);   // byte
  EXPECT_TRUE(mod->variables[1].is_signed);   // shortint
  EXPECT_TRUE(mod->variables[2].is_signed);   // int
  EXPECT_TRUE(mod->variables[3].is_signed);   // integer
  EXPECT_TRUE(mod->variables[4].is_signed);   // longint
  EXPECT_FALSE(mod->variables[5].is_signed);  // bit -> unsigned by default
}

TEST(VarDecl, VarBytePrefixEquivalentToBareByte) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  var byte a;\n"
      "  byte b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].width, mod->variables[1].width);
  EXPECT_EQ(mod->variables[0].is_signed, mod->variables[1].is_signed);
  EXPECT_EQ(mod->variables[0].is_4state, mod->variables[1].is_4state);
}

TEST(VarDecl, VarSigningOnlyElaboratesAsSignedLogic) {
  // §6.8: with the var keyword and only signing/range specified, the data type
  // is implicitly logic. `var signed [7:0]` therefore elaborates to a 4-state
  // (logic) 8-bit variable that also carries the signed qualifier -- the range-
  // only form (VarRangeOnlyEquivalentToVarLogic) stays unsigned by contrast.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  var signed [7:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_4state);
  EXPECT_TRUE(mod->variables[0].is_signed);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(VarDecl, VarRangeOnlyEquivalentToVarLogic) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  var [15:0] a;\n"
      "  var logic [15:0] b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].width, 16u);
  EXPECT_EQ(mod->variables[0].width, mod->variables[1].width);
  EXPECT_EQ(mod->variables[0].is_4state, mod->variables[1].is_4state);
  EXPECT_EQ(mod->variables[0].is_signed, mod->variables[1].is_signed);
}

}  // namespace
