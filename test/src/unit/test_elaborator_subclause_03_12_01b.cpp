#include <gtest/gtest.h>

#include <algorithm>

#include "elaborator/rtlir.h"
#include "elaborator/unit_scope_order.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_literal_dims.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(CompilationUnitScopeWrites, UnitVariableWrittenByAModuleProcedure) {
  EXPECT_TRUE(
      ElabOk("int g;\n"
             "module m;\n"
             "  logic clk;\n"
             "  initial g = 5;\n"
             "  always @(posedge clk) g <= g + 1;\n"
             "endmodule\n"));
}

TEST(CompilationUnitScopeWrites, UnitVariableWrittenByAModuleTask) {
  EXPECT_TRUE(
      ElabOk("int g;\n"
             "module m;\n"
             "  task set_g; g = 7; endtask\n"
             "  initial set_g();\n"
             "endmodule\n"));
}

TEST(CompilationUnitScopeWrites, WriteToANameDeclaredNowhereIsStillReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("int g;\n"
             "module m;\n"
             "  initial h = 5;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'h'",
                            3, "23.9"));
}

TEST(CompilationUnitScopeWrites, ModuleVariableShadowingTheUnitsIsTheModules) {
  ElabFixture f;
  auto* design = Elaborate(
      "int g = 1;\n"
      "module m;\n"
      "  int g;\n"
      "  initial g = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_NE(FindVar(design, "m", "g"), nullptr);
}

TEST(CompilationUnitScopeWrites, UnitVariableDrivenByAContinuousAssignment) {
  ElabFixture f;
  auto* design = Elaborate(
      "int g;\n"
      "module m;\n"
      "  assign g = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(FindNet(design, "m", "g"), nullptr);
}

TEST(CompilationUnitScopeWrites, NameDeclaredNowhereStillGetsAnImplicitNet) {
  ElabFixture f;
  auto* design = Elaborate(
      "int g;\n"
      "module m;\n"
      "  assign h = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_NE(FindNet(design, "m", "h"), nullptr);
}

TEST(CompilationUnitScopeOrder, UnitTaskReadsUnitVariableDeclaredAfterIt) {
  ElabFixture f;
  ElaborateSrc(
      "task t; int x; x = 5 + b; endtask\n"
      "bit b;\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'b'",
                            1, "23.9"));
}

TEST(CompilationUnitScopeOrder, ModuleWritesUnitVariableDeclaredAfterIt) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial g = 5;\n"
      "endmodule\n"
      "int g;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'g'",
                            2, "23.9"));
}

TEST(CompilationUnitScopeOrder, ModuleReadsUnitVariableDeclaredAfterIt) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial y = g;\n"
      "endmodule\n"
      "int g;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'g'", 3, "23.9"));
}

TEST(CompilationUnitScopeOrder, ModuleReadsUnitNetDeclaredAfterIt) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  initial y = w;\n"
      "endmodule\n"
      "wire w;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'w'", 3, "23.9"));
}

TEST(CompilationUnitScopeOrder,
     AssignTargetDeclaredLaterInUnitGetsImplicitNet) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  assign g = 1;\n"
      "endmodule\n"
      "int g;\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_NE(FindNet(design, "m", "g"), nullptr);
}

TEST(CompilationUnitScopeOrder, UnitScopedReferenceToLaterDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "task t; int x; x = 5 + $unit::b; endtask\n"
      "bit b;\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$unit::b' precedes its declaration", 1,
                            "3.12.1"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferenceToNothing) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial y = $unit::nope;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier '$unit::nope'", 3,
                            "3.12.1"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferencesToEarlierDataAndAnyTaskOk) {
  EXPECT_TRUE(
      ElabOk("int a;\n"
             "module m;\n"
             "  int y;\n"
             "  initial begin y = $unit::a; $unit::later_task(); end\n"
             "endmodule\n"
             "task later_task; endtask\n"));
}

TEST(CompilationUnitScopeOrder, UnitImportAfterModuleDoesNotReachIt) {
  ElabFixture f;
  ElaborateSrc(
      "package p; int x = 1; endpackage\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endmodule\n"
      "import p::*;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'x'", 4, "23.9"));
}

TEST(CompilationUnitScopeOrder, UnitImportBeforeModuleReachesIt) {
  EXPECT_TRUE(
      ElabOk("package p; int x = 1; endpackage\n"
             "import p::*;\n"
             "module m;\n"
             "  int y;\n"
             "  initial y = x;\n"
             "endmodule\n"));
}

TEST(CompilationUnitScopeOrder, ModuleVariableShadowsALaterUnitVariable) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  int y;\n"
             "  initial y = x;\n"
             "endmodule\n"
             "int x;\n"));
}

TEST(CompilationUnitScopeOrder, ModuleParameterShadowsALaterUnitVariable) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int x = 1;\n"
             "  int y;\n"
             "  initial y = x;\n"
             "endmodule\n"
             "int x;\n"));
}

TEST(CompilationUnitScopeOrder, ModuleVariableNamedLikeALaterUnitFunction) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int f;\n"
             "  int y;\n"
             "  initial y = f;\n"
             "endmodule\n"
             "function int f(); return 1; endfunction\n"));
}

TEST(CompilationUnitScopeOrder, UnitScopedCallsToLaterFunctionAndImportOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int y;\n"
             "  initial begin\n"
             "    y = $unit::later_f(2);\n"
             "    y = $unit::c_add(1);\n"
             "  end\n"
             "endmodule\n"
             "function int later_f(int a); return a; endfunction\n"
             "import \"DPI-C\" function int c_add(int a);\n"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferenceToEarlierEnumMemberOk) {
  EXPECT_TRUE(
      ElabOk("typedef enum {RED, GREEN} color_t;\n"
             "module m;\n"
             "  int y;\n"
             "  initial y = $unit::GREEN;\n"
             "endmodule\n"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferenceToLaterEnumMember) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial y = $unit::GREEN;\n"
      "endmodule\n"
      "typedef enum {RED, GREEN} color_t;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$unit::GREEN' precedes its declaration", 3,
                            "3.12.1"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferenceToEarlierClassNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; static int K = 3; endclass\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = $unit::C::K;\n"
      "endmodule\n",
      f, "m");
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "'$unit::C'", 4, "3.12.1"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferenceToLaterClass) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial y = $unit::C::K;\n"
      "endmodule\n"
      "class C; static int K = 3; endclass\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$unit::C' precedes its declaration", 3,
                            "3.12.1"));
}

TEST(CompilationUnitScopeTypes, UnitScopedArrayTypedefKeepsTheUnitsDimensions) {
  ElabFixture f;
  const RtlirDesign* design = ElaborateSrc(
      "typedef int t [2];\n"
      "module m;\n"
      "  typedef int t [3];\n"
      "  function automatic $unit::t g($unit::t a);\n"
      "    $unit::t v;\n"
      "    v = a;\n"
      "    return v;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules[0]->function_decls.size(), 1u);
  const ModuleItem* g = design->top_modules[0]->function_decls[0];
  ASSERT_FALSE(g->func_body_stmts.empty());
  EXPECT_EQ(LiteralElementCount(g->func_args[0].unpacked_dims), 2u);
  EXPECT_EQ(LiteralElementCount(g->return_array_dims), 2u);
  EXPECT_EQ(LiteralElementCount(g->func_body_stmts[0]->var_unpacked_dims), 2u);
}

TEST(CompilationUnitScopeTypes, ModuleTypedefHidesTheUnitsArrayDimensions) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "typedef int t [2];\n"
      "module m;\n"
      "  typedef struct { int a; int b; } t;\n"
      "  t v;\n"
      "  function automatic t f(t a);\n"
      "    t q;\n"
      "    q = a;\n"
      "    return q;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->unpacked_size, 0u);
  ASSERT_EQ(design->top_modules[0]->function_decls.size(), 1u);
  const ModuleItem* fn = design->top_modules[0]->function_decls[0];
  ASSERT_FALSE(fn->func_body_stmts.empty());
  EXPECT_TRUE(fn->func_args[0].unpacked_dims.empty());
  EXPECT_TRUE(fn->return_array_dims.empty());
  EXPECT_TRUE(fn->func_body_stmts[0]->var_unpacked_dims.empty());
}

TEST(CompilationUnitScopeTypes, ModuleClassHidesTheUnitsArrayTypedef) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "typedef int t [2];\n"
      "module m;\n"
      "  class t;\n"
      "    int v;\n"
      "  endclass\n"
      "  t h;\n"
      "  function automatic int g(t a);\n"
      "    t q;\n"
      "    q = a;\n"
      "    return q.v;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  const RtlirVariable* h = FindVar(design, "m", "h");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(h->unpacked_size, 0u);
  ASSERT_EQ(design->top_modules[0]->function_decls.size(), 1u);
  const ModuleItem* g = design->top_modules[0]->function_decls[0];
  ASSERT_FALSE(g->func_body_stmts.empty());
  EXPECT_TRUE(g->func_args[0].unpacked_dims.empty());
  EXPECT_TRUE(g->func_body_stmts[0]->var_unpacked_dims.empty());
}

TEST(CompilationUnitHierNames, AnInstanceOfTheCallerIsNotReachedFromRoot) {
  ElabFixture f;
  ElaborateSrc(
      "function int f();\n"
      "  return u.x;\n"
      "endfunction\n"
      "module sub;\n"
      "  int x;\n"
      "endmodule\n"
      "module top;\n"
      "  int y;\n"
      "  sub u();\n"
      "  initial y = f();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'u' in a compilation-unit task "
                            "or function is read from $root",
                            2, "3.12.1"));
}

TEST(CompilationUnitHierNames, ANameTheUnitImportsIsNoPathFromRoot) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef struct { int a; } s_t;\n"
             "  s_t s;\n"
             "endpackage\n"
             "import p::*;\n"
             "function int f();\n"
             "  return s.a;\n"
             "endfunction\n"
             "module top;\n"
             "  int y;\n"
             "  initial y = f();\n"
             "endmodule\n"));
}

TEST(CompilationUnitHierNames, AFullPathFromTheTopIsAccepted) {
  EXPECT_TRUE(
      ElabOk("function int f();\n"
             "  return top.u.x;\n"
             "endfunction\n"
             "module sub;\n"
             "  int x;\n"
             "endmodule\n"
             "module top;\n"
             "  int y;\n"
             "  sub u();\n"
             "  initial y = f();\n"
             "endmodule\n"));
}

TEST(CompilationUnitScopeOrder, EnumConstantDeclaredLaterInUnitIsUnresolved) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial y = GREEN;\n"
      "endmodule\n"
      "typedef enum {RED, GREEN} color_t;\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'GREEN'", 3, "23.9"));
}

TEST(CompilationUnitScopeOrder, ParameterDeclaredLaterInUnitIsUnresolved) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y = W;\n"
      "endmodule\n"
      "localparam int W = 8;\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'W'", 2, "23.9"));
}

TEST(CompilationUnitScopeOrder, TypedefDeclaredLaterInUnitIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  word_t v;\n"
      "endmodule\n"
      "typedef logic [15:0] word_t;\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'word_t' does not precede", 2,
                            "6.18"));
}

TEST(CompilationUnitScopeOrder, ClassDeclaredLaterInUnitIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  C h;\n"
      "endmodule\n"
      "class C;\n"
      "endclass\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'C' does not precede", 2,
                            "6.18"));
}

TEST(CompilationUnitScopeOrder, UnitConstantsDeclaredBeforeTheModuleResolve) {
  EXPECT_TRUE(
      ElabOk("typedef enum {RED, GREEN} color_t;\n"
             "localparam int W = 8;\n"
             "module m;\n"
             "  int y = W;\n"
             "  int z;\n"
             "  initial z = GREEN;\n"
             "endmodule\n"));
}

TEST(CompilationUnitScopeOrder, ModulesOwnConstantsShadowLaterUnitConstants) {
  EXPECT_TRUE(
      ElabOk("module m #(parameter int W = 1);\n"
             "  int y = W;\n"
             "endmodule\n"
             "localparam int W = 8;\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  localparam int W = 2;\n"
             "  int y = W;\n"
             "endmodule\n"
             "localparam int W = 8;\n"));
  EXPECT_TRUE(
      ElabOk("module outer;\n"
             "  localparam int W = 2;\n"
             "  module inner;\n"
             "    int y = W;\n"
             "  endmodule\n"
             "  inner i();\n"
             "endmodule\n"
             "localparam int W = 8;\n"));
}

TEST(CompilationUnitScopeOrder,
     ModulesOwnPortAndEnumConstantShadowLaterUnitOnes) {
  EXPECT_TRUE(
      ElabOk("module m(input logic [31:0] W);\n"
             "  int y;\n"
             "  initial y = W;\n"
             "endmodule\n"
             "localparam int W = 8;\n"));
  EXPECT_TRUE(
      ElabOk("module m(W);\n"
             "  input [31:0] W;\n"
             "  int y;\n"
             "  initial y = W;\n"
             "endmodule\n"
             "localparam int W = 8;\n"));
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {GREEN} c_t;\n"
      "  int y;\n"
      "  initial y = GREEN;\n"
      "endmodule\n"
      "typedef enum {RED, GREEN} color_t;\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const RtlirModule* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(std::ranges::count_if(
                m->variables,
                [](const RtlirVariable& v) { return v.name == "GREEN"; }),
            1);
}

TEST(CompilationUnitScopeOrder, ModuleDeclaresNameReadsTheModulesOwnNames) {
  auto r = Parse(
      "module m #(parameter int P = 1)(input int q);\n"
      "  localparam int L = 2;\n"
      "  typedef enum {GREEN} c_t;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const ModuleDecl* decl = r.cu->modules[0];
  EXPECT_TRUE(ModuleDeclaresName(decl, "P"));
  EXPECT_TRUE(ModuleDeclaresName(decl, "q"));
  EXPECT_TRUE(ModuleDeclaresName(decl, "L"));
  EXPECT_TRUE(ModuleDeclaresName(decl, "GREEN"));
  EXPECT_FALSE(ModuleDeclaresName(decl, "W"));
}

}  // namespace
