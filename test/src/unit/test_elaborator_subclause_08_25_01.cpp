#include <gtest/gtest.h>

#include <initializer_list>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_literal_dims.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(ParameterizedScopeResolutionElaboration,
     SpecificSpecializationAccessesTypeParamOk) {
  EXPECT_TRUE(
      ElabOk("class C #(type T = int);\n"
             "endclass\n"
             "module m;\n"
             "  C#(integer)::T x;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     BothClassAndLocalParamsAccessibleOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int a, b;\n"
             "  initial begin\n"
             "    a = C#()::p;\n"
             "    b = C#()::q;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     OutOfBlockMethodForParameterizedClassOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  extern static function int f();\n"
             "endclass\n"
             "function int C::f();\n"
             "  return p;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration, MultipleSpecializationsAccessOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int a, b;\n"
             "  initial begin\n"
             "    a = C#(3)::p;\n"
             "    b = C#(7)::p;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeOutsideIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInContAssignIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  assign result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInNestedExprIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = 1 + C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInAlwaysCombIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  always_comb result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeInsideClassOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "  static function int g();\n"
             "    return C::q;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     SpecializationParameterFoldsInsideAGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 1);\n"
      "endclass\n"
      "module m;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam int W = C#(4)::p;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto* w = FindParam(design, "m", "W");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_resolved);
  EXPECT_EQ(w->resolved_value, 4);
}

TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeInForkArmIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial fork\n"
      "    result = C::q;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 7, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInForInitializationIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  int i;\n"
      "  initial for (result = C::q; i < 2; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 7, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeInForStepIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 2; result = C::q) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 7, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInAssertionPassStmtIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial assert (1) result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInAssertionFailStmtIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial assert (1) else result = C::q;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 6, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInRandcaseItemIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : result = C::q;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 8, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInRandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { result = C::q; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 8, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInAVariableDeclarationInitializerIsError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "endclass\n"
      "module m;\n"
      "  int x = C::p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "used as scope resolution prefix for parameterized class", 4, "8.25.1"));
}

TEST(ParameterizedScopeResolutionElaboration,
     ExplicitDefaultSpecializationInAVariableDeclarationInitializerOk) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "endclass\n"
      "module m;\n"
      "  int x = C#()::p;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedPrefixOutsideTheClassIsAnError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  static function int f(); return p; endfunction\n"
      "endclass\n"
      "package q;\n"
      "  int a = C::p;\n"
      "  task t(output int o); o = C::p; endtask endpackage\n"
      "class D;\n"
      "  function int g(); return C::f(); endfunction\n"
      "  class N; function int n(); return C::p; endfunction endclass\n"
      "endclass\n"
      "class E #(int r = 2);\n"
      "  function int own(); return E::r; endfunction\n"
      "  class I; function int i(); return E::r; endfunction endclass\n"
      "endclass\n"
      "module m;\n"
      "  function int h(); return C::p; endfunction\n"
      "  int ok = C#()::p;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {5, 6, 8, 9, 16}) {
    EXPECT_TRUE(ReportedError(diags,
                              "unadorned name 'C' used as scope resolution "
                              "prefix for parameterized class",
                              kLine, "8.25.1"))
        << kLine;
  }
  for (const int kLine : {12, 13, 17}) {
    EXPECT_FALSE(ReportedError(diags, "unadorned name", kLine, "8.25.1"))
        << kLine;
  }
}

TEST(ParameterizedScopeResolutionElaboration,
     ATypeBehindAnUnadornedPrefixOutsideTheClassIsAnError) {
  ElabFixture f;
  ElabOk(
      "class C #(int p = 1);\n"
      "  typedef int T;\n"
      "  C::T own;\n"
      "  class N; C::T n; endclass\n"
      "  extern function C::T f(C::T a);\n"
      "endclass\n"
      "function C::T C::f(C::T a); return a; endfunction\n"
      "package q; typedef C::T qt; endpackage\n"
      "class D;\n"
      "  C::T d;\n"
      "  function void g(C::T a); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C::T x;\n"
      "  C#()::T y;\n"
      "  C#(3)::T z;\n"
      "  initial begin C::T b; end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kMessage =
      "unadorned name 'C' used as scope resolution prefix for parameterized "
      "class";
  for (const int kLine : {8, 10, 11, 14, 17}) {
    EXPECT_TRUE(ReportedError(diags, kMessage, kLine, "8.25.1")) << kLine;
  }
  for (const int kLine : {3, 4, 5, 7, 15, 16}) {
    EXPECT_FALSE(ReportedError(diags, kMessage, kLine, "8.25.1")) << kLine;
  }
}

TEST(ParameterizedScopeResolutionElaboration,
     SubroutineDeclarationsTakeTheSpecializationsDimensions) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "class C #(int p = 1);\n"
      "  typedef int t [p];\n"
      "  typedef logic [p-1:0] w;\n"
      "endclass\n"
      "module m;\n"
      "  localparam int p = 9;\n"
      "  function automatic C#(5)::t g(C#(4)::t a, C#(4)::w b);\n"
      "    C#(3)::t v;\n"
      "    v[0] = a[0] + b;\n"
      "    return '{default: v[0]};\n"
      "  endfunction\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules[0]->function_decls.size(), 1u);
  const ModuleItem* g = design->top_modules[0]->function_decls[0];
  ASSERT_EQ(g->func_args.size(), 2u);
  ASSERT_FALSE(g->func_body_stmts.empty());
  EXPECT_EQ(LiteralElementCount(g->return_array_dims), 5u);
  EXPECT_EQ(LiteralElementCount(g->func_args[0].unpacked_dims), 4u);
  EXPECT_TRUE(g->func_args[1].unpacked_dims.empty());
  EXPECT_EQ(LiteralElementCount(g->func_body_stmts[0]->var_unpacked_dims), 3u);
}

}  // namespace
