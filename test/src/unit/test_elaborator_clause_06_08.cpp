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

TEST(VarDecl, IntIsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_signed);
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

// §6.8: `var` with implicit type elaborates as logic (1-bit, 4-state).
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
  EXPECT_EQ(mod->variables[0].width, 1u);
  EXPECT_TRUE(mod->variables[0].is_4state);
}

// §6.8: `var` with range elaborates as logic vector.
TEST(VarDecl, VarWithRangeElaboratesAsLogicVector) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  var [7:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_EQ(mod->variables[0].width, 8u);
  EXPECT_TRUE(mod->variables[0].is_4state);
}

// §6.8: byte is signed by default.
TEST(VarDecl, ByteIsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_signed);
}

// §6.8: shortint is signed by default.
TEST(VarDecl, ShortintIsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint si;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_signed);
}

// §6.8: longint is signed by default.
TEST(VarDecl, LongintIsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  longint li;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_signed);
}

// §6.8: integer is signed by default.
TEST(VarDecl, IntegerIsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer ig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_signed);
}

// §6.8: logic is unsigned by default.
TEST(VarDecl, LogicIsUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->variables[0].is_signed);
}

// §6.8: bit is unsigned by default.
TEST(VarDecl, BitIsUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->variables[0].is_signed);
}

// §6.8 footnote 14: a data_declaration that is not within a procedural
// context shall not use the automatic keyword. Package items are
// non-procedural, so an automatic variable inside a package is illegal.
TEST(VarDecl, AutomaticInPackageIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  automatic int x;\n"
      "endpackage\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.8 footnote 14: a static variable inside a package is allowed —
// the rule only forbids the automatic keyword in non-procedural contexts.
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

// §6.8 footnote 14: positive counterpart — the automatic keyword is permitted
// when the data_declaration sits inside a procedural context. An initial
// block is procedural, so the elaborator must accept the form unchanged.
TEST(VarDecl, AutomaticInProceduralBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x = 5;\n"
             "  end\n"
             "endmodule\n"));
}

// §6.8 footnote 17: applying a packed dimension to a struct type is
// only legal when the struct is also marked packed; the elaborator
// must reject the unpacked-struct + packed-dim combination.
TEST(VarDecl, StructPackedDimWithoutPackedKeywordIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct { int x; } [3:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.8 footnote 17: same rule for union — a packed dimension on an
// unpacked union is illegal.
TEST(VarDecl, UnionPackedDimWithoutPackedKeywordIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  union { int x; logic [31:0] y; } [3:0] u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.8 footnote 17: a packed struct accepts a packed dimension; this
// is the legal counterpart to the negative test above and confirms the
// rule fires only when the packed keyword is missing.
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

// §6.8 footnote 17: same legal counterpart for union — once the packed
// keyword is present, applying a packed dimension is allowed.
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

// §6.8 footnote 18: when a type_reference is used in a net declaration it
// must be preceded by a net type keyword. Confirm at the elaborator stage
// that the legal form `wire type(x) y;` survives elaboration.
TEST(VarDecl, TypeRefInNetDeclWithWireOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire x;\n"
             "  wire type(x) y;\n"
             "endmodule\n"));
}

// §6.8 footnote 18: the variable-declaration counterpart — `var type(x) y;`
// elaborates cleanly because the var keyword satisfies the rule.
TEST(VarDecl, TypeRefInVarDeclWithVarOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  var type(x) y;\n"
             "endmodule\n"));
}

// §6.8 example: `var byte my_byte;` is "equivalent to" the bare form
// `byte my_byte;`. Elaborating both side-by-side must produce variables
// with matching width, signedness, and 4-state classification — the var
// prefix may not change any observable property when the data_type is
// already explicit.
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

// §6.8 example: `var [15:0] vw;` is "equivalent to" `var logic [15:0] vw;`.
// With only a range supplied, the implicit data type is logic, so both
// forms must produce identical 16-bit 4-state variables.
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
