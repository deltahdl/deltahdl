#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(VarDecl, ConstWithoutInitializerIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "const variable 'x' must be initialized", 2,
                            "6.20.6"));
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
  ElaborateSrcAllowingParseErrors(
      "package p;\n"
      "  automatic int x;\n"
      "endpackage\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'automatic' is not allowed in a data_declaration outside", 2, "6.8"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "packed dimension on struct requires the packed keyword", 2, "7.2"));
}

TEST(VarDecl, UnionPackedDimWithoutPackedKeywordIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  union { int x; logic [31:0] y; } [3:0] u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "packed dimension on union requires the packed keyword", 2, "7.2"));
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
  EXPECT_TRUE(mod->variables[0].is_signed);
  EXPECT_TRUE(mod->variables[1].is_signed);
  EXPECT_TRUE(mod->variables[2].is_signed);
  EXPECT_TRUE(mod->variables[3].is_signed);
  EXPECT_TRUE(mod->variables[4].is_signed);
  EXPECT_FALSE(mod->variables[5].is_signed);
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

TEST(VarDecl, AutomaticInEveryNonProceduralPlaceIsError) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "interface i;\n"
      "  automatic int x;\n"
      "endinterface\n"
      "program p;\n"
      "  automatic int x;\n"
      "endprogram\n"
      "checker c;\n"
      "  automatic int x;\n"
      "endchecker\n"
      "module t;\n"
      "  for (genvar k = 0; k < 2; k++) begin : g\n"
      "    automatic int x;\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : h\n"
      "      automatic int y;\n"
      "    end\n"
      "  endcase\n"
      "  if (1)\n"
      "    automatic int z;\n"
      "  var automatic logic v;\n"
      "  const automatic int c = 1;\n"
      "  const var automatic int d = 2;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2U, 5U, 8U, 12U, 16U, 20U, 21U, 22U, 23U}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "'automatic' is not allowed in a data_declaration outside", line,
        "6.8"));
  }
}

TEST(VarDecl, AutomaticInEveryProceduralPlaceOk) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  task m();\n"
      "    automatic int a;\n"
      "  endtask\n"
      "endclass\n"
      "interface i;\n"
      "  initial begin automatic int x; end\n"
      "endinterface\n"
      "program p;\n"
      "  initial begin automatic int x; end\n"
      "endprogram\n"
      "checker c;\n"
      "  initial begin automatic int x; end\n"
      "endchecker\n"
      "module t;\n"
      "  task k();\n"
      "    automatic int x;\n"
      "  endtask\n"
      "  function void fn();\n"
      "    automatic int y;\n"
      "  endfunction\n"
      "  logic clk;\n"
      "  initial fork automatic int z; join\n"
      "  always @(posedge clk) begin : b\n"
      "    automatic int w;\n"
      "  end\n"
      "  initial begin\n"
      "    var automatic logic v;\n"
      "    const automatic int c = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(VarDecl, DISABLED_AutomaticInCompilationUnitIsError) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "automatic int x;\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'automatic' is not allowed in a data_declaration outside", 1, "6.8"));
}

TEST(VarDecl, DISABLED_AutomaticClassPropertyIsError) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "class C;\n"
      "  automatic int x;\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'automatic' is not allowed in a data_declaration outside", 2, "6.8"));
}

TEST(VarDecl, StructWithoutPackedKeywordIsErrorInEveryPlace) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "struct { int a; } [1:0] cu;\n"
      "package p;\n"
      "  struct { int a; } [1:0] s;\n"
      "endpackage\n"
      "program q;\n"
      "  struct { int a; } [1:0] s;\n"
      "endprogram\n"
      "class C;\n"
      "  union { int a; int b; } [1:0] u;\n"
      "endclass\n"
      "interface i;\n"
      "  struct { int a; } [1:0] s;\n"
      "  typedef union { int a; } [1:0] U;\n"
      "endinterface\n"
      "checker c;\n"
      "  struct { int a; } [1:0] s;\n"
      "endchecker\n"
      "module t(input struct { logic a; } [1:0] pt);\n"
      "  typedef struct { int a; } [1:0] T;\n"
      "  function void fn(struct { int a; } [1:0] s);\n"
      "  endfunction\n"
      "  if (1) begin : g\n"
      "    struct { int a; } [1:0] s;\n"
      "  end\n"
      "  initial begin\n"
      "    struct { int a; } [1:0] s;\n"
      "  end\n"
      "  q qq();\n"
      "  i ii();\n"
      "  c cc();\n"
      "  struct { struct { int y; } [1:0] m; } s2;\n"
      "  function struct { int a; } [1:0] fr();\n"
      "  endfunction\n"
      "  task tk(input struct { int a; } [1:0] a);\n"
      "  endtask\n"
      "  initial begin\n"
      "    automatic struct { int a; } [1:0] s;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line :
       {1U, 3U, 6U, 12U, 16U, 18U, 19U, 20U, 23U, 26U, 31U, 32U, 34U, 37U}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "packed dimension on struct requires the packed keyword", line, "7.2"));
  }
  for (uint32_t line : {9U, 13U}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "packed dimension on union requires the packed keyword", line, "7.2"));
  }
}

TEST(VarDecl, PackedStructWithPackedDimOkInAnInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface i;\n"
      "  struct packed { int a; } [1:0] s;\n"
      "  typedef union packed { int a; } [1:0] U;\n"
      "endinterface\n"
      "module t;\n"
      "  i ii();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(VarDecl, BareNameInProcedureStaysAnExpressionStatement) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'x' names a variable or a net, and a call names a",
                            4, "A.8.2"));
}

}  // namespace
