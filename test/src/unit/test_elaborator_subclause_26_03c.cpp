#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace {

TEST(PackageImport, RangedEnumConstantsAreProvidedThroughAWildcardExport) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3]} t;\n"
             "endpackage\n"
             "package p2;\n"
             "  import p1::*;\n"
             "  export p1::*;\n"
             "  int seen = VAL1 + VAL2;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p2::VAL2 + p2::VAL1;\n"
             "endmodule\n"));
}

TEST(PackageScopeReference, WrittenNameOfARangedMemberIsNoDeclaration) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3]} t;\n"
             "endpackage\n"
             "module top;\n"
             "  int r;\n"
             "  initial r = p1::VAL2;\n"
             "  initial r = p1::VAL;\n"
             "endmodule\n",
             f));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "reference to 'p1::VAL2', which package 'p1' "
                             "neither declares nor exports",
                             6, "26.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'p1::VAL', which package 'p1' "
                            "neither declares nor exports",
                            7, "26.3"));
}

TEST(PackageImport, BareRangedEnumConstantResolvesThroughAWildcardImport) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3], W[3:1]} t;\n"
             "endpackage\n"
             "module top;\n"
             "  import p1::*;\n"
             "  int r;\n"
             "  initial r = VAL2 + W1;\n"
             "endmodule\n"));
}

TEST(PackageImport, ExplicitImportOfARangedEnumConstantIsClean) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef enum {VAL[3]} t;\n"
             "endpackage\n"
             "module top;\n"
             "  import p1::VAL2;\n"
             "  int r;\n"
             "  initial r = VAL2;\n"
             "endmodule\n"));
}

TEST(PackageImport, GeneratedEnumConstantsOfTwoImportsAreAmbiguous) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  typedef enum {VAL[2]} t;\n"
             "endpackage\n"
             "package q;\n"
             "  typedef enum {VAL[2]} u;\n"
             "endpackage\n"
             "module top;\n"
             "  import p::*;\n"
             "  import q::*;\n"
             "  int r;\n"
             "  initial r = VAL1;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'VAL1' is ambiguous between wildcard "
                            "imports of packages 'p' and 'q'",
                            11, "26.3"));
}

TEST(PackageImport, BareEnumDataDeclarationLiteralsComeThroughAWildcardImport) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  enum {X, Y} v;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  int a = Y;\n"
      "  localparam int L = Y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_NE(FindVar(design, "m", "Y"), nullptr);
  const auto* l = FindParam(design, "m", "L");
  ASSERT_NE(l, nullptr);
  EXPECT_TRUE(l->is_resolved);
  EXPECT_EQ(l->resolved_value, 1);
}

TEST(PackageImport, ASharedEnumDeclarationImportsItsLiteralsOnce) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  enum {X, Y} v, w;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  int a = Y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(CountVarsEndingIn(design, "m", "Y"), 1u);
}

TEST(PackageImport, OwnGeneratedEnumConstantShadowsAWildcardImportsInAPackage) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum {VAL[2] = 5} t;\n"
      "endpackage\n"
      "package q;\n"
      "  typedef enum {VAL[2]} u;\n"
      "  import p::*;\n"
      "  localparam int L = VAL1;\n"
      "endpackage\n"
      "module top;\n"
      "  localparam int M = q::L;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* m = FindParam(design, "top", "M");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_resolved);
  EXPECT_EQ(m->resolved_value, 1);
}

TEST(PackageScopeReference, PackageQualifiedClassDeclaresAHandleWithoutImport) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  class C;\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  p::C c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "p::C");
}

TEST(PackageScopeReference, AnImportedTypedefNamesItsOwnPackagesTypedef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q; typedef logic [1:0] T; endpackage\n"
      "package p;\n"
      "  typedef logic [3:0] C; typedef C B; typedef q::T S;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  typedef B C;\n"
      "  typedef logic [8:0] T;\n"
      "  C x; S y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 4u);
  const RtlirVariable* y = FindVar(design, "m", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 2u);
}

TEST(PackageScopeReference, AnImportedTypedefChainEndingAtAPackageClass) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "package p; class K; virtual ifc vif; endclass typedef K C; "
      "typedef C B; endpackage\n"
      "module top;\n"
      "  import p::*;\n"
      "  typedef B C;\n"
      "  C x = new;\n"
      "  initial if (0) x.vif.t();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PackageScopeReference, AmbiguousWildcardReadInAFunctionBody) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p; int c = 1; endpackage\n"
             "package q; int c = 2; endpackage\n"
             "module m;\n"
             "  function int f();\n"
             "    import p::*;\n"
             "    import q::*;\n"
             "    return c;\n"
             "  endfunction\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'c' is ambiguous between wildcard "
                            "imports of packages 'p' and 'q'",
                            7, "26.3"));
}

TEST(PackageScopeReference, DeclarationAfterAWildcardClaimInATaskBody) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p; int c = 1; endpackage\n"
             "module m;\n"
             "  int r;\n"
             "  task t();\n"
             "    import p::*;\n"
             "    int a = c;\n"
             "    int c;\n"
             "    r = a;\n"
             "  endtask\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'c' follows a reference resolved "
                            "through a wildcard package import",
                            7, "26.3"));
}

TEST(PackageScopeReference, ExplicitImportBesideALocalInAFunctionBody) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p; int c = 1; endpackage\n"
             "module m;\n"
             "  function int f(int c);\n"
             "    import p::c;\n"
             "    return c;\n"
             "  endfunction\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit import of 'p::c' collides with existing "
                            "declaration of 'c'",
                            4, "26.3"));
}

TEST(PackageScopeReference, FunctionBodyImportElaborates) {
  EXPECT_TRUE(
      ElabOk("package p; int c = 1; endpackage\n"
             "module m;\n"
             "  function automatic int f(int a);\n"
             "    import p::*;\n"
             "    int v = a;\n"
             "    return v + c;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(PackageImport, ImportedNettypeDeclaresANetOfThePackagesNettype) {
  ElabFixture f;
  auto* design = Elaborate(
      "package P;\n"
      "  function automatic logic pres(input logic d[]);\n"
      "    return d[0] & d[1];\n"
      "  endfunction\n"
      "  nettype logic nt with pres;\n"
      "endpackage\n"
      "module e;\n"
      "  import P::nt;\n"
      "  nt w;\n"
      "endmodule\n"
      "module m;\n"
      "  import P::*;\n"
      "  nettype P::nt pnt;\n"
      "  nt n;\n"
      "  pnt a;\n"
      "  tran sw(n, a);\n"
      "  e u();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  for (const auto& [mod, name] :
       {std::pair<std::string_view, std::string_view>{"m", "n"}, {"e", "w"}}) {
    const RtlirNet* net = FindNet(design, mod, name);
    ASSERT_NE(net, nullptr) << name;
    EXPECT_TRUE(net->is_user_nettype) << name;
    EXPECT_EQ(net->resolve_func, "P::pres") << name;
  }
}

TEST(PackageImport, ANestedProgramCallsATaskItsModuleWildcardImports) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  task automatic set_v(output logic [7:0] o); o = 8'd99; endtask\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  logic [7:0] v;\n"
      "  program p;\n"
      "    initial set_v(v);\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PackageImport, ANestedProgramCallsATaskItsModuleExplicitlyImports) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  task automatic set_v(output logic [7:0] o); o = 8'd99; endtask\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::set_v;\n"
      "  logic [7:0] v;\n"
      "  program p;\n"
      "    initial set_v(v);\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PackageImport, ANestedProgramCallsATaskAnOuterModuleImports) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  task automatic set_v(output logic [7:0] o); o = 8'd99; endtask\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  module mid;\n"
      "    logic [7:0] v;\n"
      "    program p;\n"
      "      initial set_v(v);\n"
      "    endprogram\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PackageImport, ANestedProgramCallsATaskItsModuleExplicitlyImportsBelowIt) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  task automatic set_v(output logic [7:0] o); o = 8'd99; endtask\n"
      "endpackage\n"
      "module top;\n"
      "  logic [7:0] v;\n"
      "  program p;\n"
      "    initial set_v(v);\n"
      "  endprogram\n"
      "  import pkg::set_v;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PackageImport, ANestedProgramWritesNoVariableItsModuleImportsBelowIt) {
  for (const char* imported : {"pkg::w", "pkg::*"}) {
    ElabFixture f;
    ElaborateSrc(std::string("package pkg;\n"
                             "  int w;\n"
                             "endpackage\n"
                             "module top;\n"
                             "  program p;\n"
                             "    initial w = 1;\n"
                             "  endprogram\n"
                             "  import ") +
                     imported +
                     ";\n"
                     "endmodule\n",
                 f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'w'",
                              6, "23.9"))
        << imported;
  }
}

TEST(PackageScopeReference,
     PackageScopedArrayTypedefKeepsThePackagesDimensions) {
  ElabFixture f;
  const RtlirDesign* design = ElaborateSrc(
      "package p; typedef int t [2]; endpackage\n"
      "module m;\n"
      "  typedef int t [3];\n"
      "  task automatic k(input p::t a, output int n);\n"
      "    p::t v;\n"
      "    v = a;\n"
      "    n = v[1];\n"
      "  endtask\n"
      "  function automatic p::t g(); return '{4, 5}; endfunction\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  const std::vector<ModuleItem*>& subroutines =
      design->top_modules[0]->function_decls;
  ASSERT_EQ(subroutines.size(), 2u);
  ASSERT_FALSE(subroutines[0]->func_body_stmts.empty());
  auto expect_two_elements = [](const std::vector<Expr*>& dims) {
    ASSERT_EQ(dims.size(), 1u);
    EXPECT_EQ(dims[0]->int_val, 2u);
  };
  expect_two_elements(subroutines[0]->func_args[0].unpacked_dims);
  expect_two_elements(subroutines[0]->func_body_stmts[0]->var_unpacked_dims);
  expect_two_elements(subroutines[1]->return_array_dims);
}

}  // namespace
