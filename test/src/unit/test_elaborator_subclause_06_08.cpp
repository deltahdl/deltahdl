// Tests for §6.8 "Variable declarations". The subclause states what a variable
// is, gives Syntax 6-3, and carries three footnotes that restrict what a
// declaration may say: footnote 14 forbids the automatic keyword outside a
// procedural context, footnote 17 requires the packed keyword beside a packed
// dimension, and footnote 18 requires a net or var keyword before a
// type_reference.

#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.20.6, not §6.8, is what a const without an initializer breaches: §6.8
// says only that "A variable can be declared with an initializer", while
// §6.20.6 "Const constants" is where the requirement to initialize one lives.
TEST(VarDecl, ConstWithoutInitializerIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "const variable 'x' must be initialized");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.20.6");
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

// §6.8 footnote 14 to Syntax 6-3: "In a data_declaration that is not within a
// procedural context, it shall be illegal to use the automatic keyword." A
// package-level variable declaration is such a data_declaration. The report
// naming §6.8 is the parser's, raised in Parser::ParseDataDeclItem where the
// keyword is read, which ElaborateSrc leaves in the fixture's engine.
TEST(VarDecl, AutomaticInPackageIsError) {
  ElabFixture f;
  // §6.8's rule against a lifetime keyword here is the parser's, so the source
  // does not parse and the permissive helper says that is meant.
  ElaborateSrcAllowingParseErrors(
      "package p;\n"
      "  automatic int x;\n"
      "endpackage\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "'automatic' is not allowed in a data_declaration outside");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.8");
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

// §7.2 footnote 17 to Syntax 7-1, not §6.8 footnote 17, is what the report
// names: §7.2 states the rule in the form the elaborator implements, adding
// that a packed dimension on a union may take soft instead of packed.
TEST(VarDecl, StructPackedDimWithoutPackedKeywordIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct { int x; } [3:0] s;\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "packed dimension on struct requires the packed keyword");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "7.2");
}

// The union half of the same §7.2 footnote 17.
TEST(VarDecl, UnionPackedDimWithoutPackedKeywordIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  union { int x; logic [31:0] y; } [3:0] u;\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "packed dimension on union requires the packed keyword");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "7.2");
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

// §6.8 on the initial value a static variable may take: "Initial values are
// not constrained to simple constants; they can include run-time expressions,
// including dynamic memory allocation. For example, a static class handle or a
// mailbox can be created and initialized by calling its new method (see
// 15.4.1), or static variables can be initialized to random values by calling
// the $urandom system task."
//
// The three tests below hold that for a static variable declared inside a
// subroutine, which is where the elaborator used to require a constant
// expression. Nothing narrows §6.8 there: §6.21 constrains only when the
// initialization runs, once at the beginning of simulation, and §13.4.2
// covers storage and reentrancy.

// $urandom is the example §6.8 names, so this is the standard's own case.
TEST(StaticVariableInitializers, SubroutineStaticTakesASystemCallInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function automatic int f();\n"
      "    static int x = $urandom;\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A parameter reference is a constant expression by §11.2.1, so this source
// was legal even under the rule the elaborator used to state. It was rejected
// anyway, because the constancy test was called without a scope and so
// answered false for every identifier. Keeping the case distinguishes a
// literal from a constant expression, which a literal initializer cannot.
TEST(StaticVariableInitializers, SubroutineStaticTakesAParameterInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P = 4;\n"
      "  function automatic int f();\n"
      "    static int x = P;\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// An argument of an automatic function has no value until the call, so this
// is a run-time expression in the plainest sense, and §6.8 admits it.
TEST(StaticVariableInitializers,
     SubroutineStaticTakesARunTimeExpressionInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function automatic int f(int a);\n"
      "    static int x = a;\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
