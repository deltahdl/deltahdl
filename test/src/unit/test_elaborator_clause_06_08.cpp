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
  EXPECT_EQ(mod->variables[0].name, "t.a");
  EXPECT_EQ(mod->variables[1].name, "t.b");
  EXPECT_EQ(mod->variables[2].name, "t.c");
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
