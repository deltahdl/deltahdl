#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <optional>
#include <string>
#include <utility>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_literal_dims.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(ClassScopeResolutionElaboration, ANonStaticMemberIsNotReachedFromOutside) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  parameter int P = 3;\n"
      "  int x = 5;\n"
      "  static int s = 7;\n"
      "  function int f(); return 1; endfunction\n"
      "  static function int g(); return 2; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = C::x;\n"
      "    y = C::f();\n"
      "    y = C::s + C::g() + C::P;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (auto [line, member] :
       std::initializer_list<std::pair<uint32_t, const char*>>{{11u, "x"},
                                                               {12u, "f"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("cannot reach non-static member '") +
                                  member +
                                  "' through the class scope operator from "
                                  "outside its class",
                              line, "8.23"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ClassScopeResolutionElaboration, TheConstructorIsReachedFromOutside) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new(int v); x = v; endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  function new(int v); super.new(v); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = D::new(4);\n"
      "    c = C::new(5);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(ClassScopeResolutionElaboration, ScopedTypedefTakesNoModuleArrayDims) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m;\n"
      "  typedef logic my_type [2];\n"
      "  Cfg::my_type x;\n"
      "  initial x = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  const auto* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 32u);
}

TEST(ClassScopeResolutionElaboration,
     ChainOfNestedClassesIsWalkedFromItsFirstName) {
  ElabFixture f;
  ElaborateSrc(
      "class Base; endclass\n"
      "class B;\n"
      "  class C; endclass\n"
      "endclass\n"
      "class A;\n"
      "  class B;\n"
      "    class C extends Base; endclass\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  A::B::C h; B::C g;\n"
      "  let lb(Base x) = 1;\n"
      "  let lc(A::B::C x) = 1;\n"
      "  initial begin\n"
      "    $display(\"%0d\", lb(h) + lc(h));\n"
      "    $display(\"%0d\", lb(g));\n"
      "    $display(\"%0d\", lc(g));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             15, "11.12"));
  for (uint32_t line : {16u, 17u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal",
                              line, "11.12"));
  }
}

TEST(ClassScopeResolutionElaboration, NestedClassParameterIsAConstant) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Outer;\n"
      "  class Inner;\n"
      "    localparam int N = 5;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  localparam int A = Outer::Inner::N;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "A"), 5);
}

TEST(ClassScopeResolutionElaboration, NestedModuleClassParameterSizesAVar) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class Outer;\n"
      "    class Inner;\n"
      "      localparam int N = 5;\n"
      "    endclass\n"
      "  endclass\n"
      "  logic [Outer::Inner::N-1:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 5u);
}

TEST(ClassScopeResolutionElaboration, SelectInAScopedChainHasNoKey) {
  EvalFixture f;
  ScopeMap scope{{"a.b", 3}};
  auto* e = ParseExprFrom("a[0].b", f);
  EXPECT_EQ(ConstEvalInt(e, scope), std::nullopt);
  EXPECT_FALSE(IsConstantExpr(e, scope));
}

TEST(ClassScopeResolutionElaboration, ChainedTypedefTakesTheNestedClassesDims) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "class Inner;\n"
      "  typedef int t [2];\n"
      "endclass\n"
      "class Outer;\n"
      "  class Inner;\n"
      "    typedef int t [3];\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  function automatic Outer::Inner::t g(Outer::Inner::t a);\n"
      "    Outer::Inner::t v;\n"
      "    v = a;\n"
      "    return v;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules[0]->function_decls.size(), 1u);
  const ModuleItem* g = design->top_modules[0]->function_decls[0];
  ASSERT_FALSE(g->func_body_stmts.empty());
  EXPECT_EQ(LiteralElementCount(g->return_array_dims), 3u);
  EXPECT_EQ(LiteralElementCount(g->func_args[0].unpacked_dims), 3u);
  EXPECT_EQ(LiteralElementCount(g->func_body_stmts[0]->var_unpacked_dims), 3u);
}

TEST(ClassScopeResolutionElaboration, UnitLedChainTakesTheUnitClassesDims) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "class C;\n"
      "  typedef int t [2];\n"
      "endclass\n"
      "module m;\n"
      "  function automatic int g($unit::C::t a);\n"
      "    return a[0];\n"
      "  endfunction\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules[0]->function_decls.size(), 1u);
  const ModuleItem* g = design->top_modules[0]->function_decls[0];
  EXPECT_EQ(LiteralElementCount(g->func_args[0].unpacked_dims), 2u);
}

const char* const kNestedSpecializationClasses =
    "class Inner #(int p = 1);\n"
    "  typedef int t [p + 10];\n"
    "endclass\n"
    "class Outer;\n"
    "  class Inner #(int p = 1);\n"
    "    typedef int t [p];\n"
    "  endclass\n"
    "endclass\n";

TEST(ClassScopeResolutionElaboration, ChainedSpecializationIsTheNestedClasses) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      std::string(kNestedSpecializationClasses) +
          "module m;\n"
          "  Outer::Inner#(4)::t v;\n"
          "  function automatic Outer::Inner#(5)::t g(Outer::Inner#(3)::t a);\n"
          "    Outer::Inner#(2)::t q;\n"
          "    q[0] = a[0];\n"
          "    return '{default: q[0]};\n"
          "  endfunction\n"
          "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->unpacked_size, 4u);
  ASSERT_EQ(design->top_modules[0]->function_decls.size(), 1u);
  const ModuleItem* g = design->top_modules[0]->function_decls[0];
  ASSERT_FALSE(g->func_body_stmts.empty());
  EXPECT_EQ(LiteralElementCount(g->return_array_dims), 5u);
  EXPECT_EQ(LiteralElementCount(g->func_args[0].unpacked_dims), 3u);
  EXPECT_EQ(LiteralElementCount(g->func_body_stmts[0]->var_unpacked_dims), 2u);
}

TEST(ClassScopeResolutionElaboration, PackageSpecializationIsThePackagesClass) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(std::string(kNestedSpecializationClasses) +
                                         "package pkg;\n"
                                         "  class Inner #(int p = 1);\n"
                                         "    typedef int t [p + 20];\n"
                                         "  endclass\n"
                                         "endpackage\n"
                                         "module m;\n"
                                         "  pkg::Inner#(4)::t w;\n"
                                         "  function automatic int g();\n"
                                         "    pkg::Inner#(4)::t q;\n"
                                         "    return q[0];\n"
                                         "  endfunction\n"
                                         "endmodule\n",
                                     f, "m");
  ASSERT_NE(design, nullptr);
  const RtlirVariable* w = FindVar(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->unpacked_size, 24u);
  ASSERT_EQ(design->top_modules[0]->function_decls.size(), 1u);
  const ModuleItem* g = design->top_modules[0]->function_decls[0];
  ASSERT_FALSE(g->func_body_stmts.empty());
  EXPECT_EQ(LiteralElementCount(g->func_body_stmts[0]->var_unpacked_dims), 24u);
}

TEST(ClassScopeResolutionElaboration, ChainReachingNoClassIsNotSpecialized) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(std::string(kNestedSpecializationClasses) +
                                         "module m;\n"
                                         "  Outer::Missing::Inner#(4)::t w;\n"
                                         "endmodule\n",
                                     f, "m");
  ASSERT_NE(design, nullptr);
  const RtlirVariable* w = FindVar(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->unpacked_size, 0u);
}

TEST(ClassScopeResolutionElaboration, ChainedTypeIsTheNestedClassesTypedef) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "class Inner;\n"
      "  typedef logic [3:0] s;\n"
      "  int x;\n"
      "endclass\n"
      "class Outer;\n"
      "  class Inner;\n"
      "    typedef logic [7:0] s;\n"
      "    typedef logic [5:0] u;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  Outer::Inner::s v;\n"
      "  Outer::Inner::u w;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "class 'Inner' declares no type 'u'", 13, "8.23"));
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);
  const RtlirVariable* w = FindVar(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->width, 6u);
}

TEST(ClassScopeResolutionElaboration, PackageClassTypedefTakesItsType) {
  ElabFixture f;
  RtlirDesign* design = ElaborateSrc(
      "package pkg;\n"
      "  class C;\n"
      "    typedef logic [5:0] t;\n"
      "    typedef logic [4:0] u;\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  pkg::C::t v;\n"
      "  C::u w;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 6u);
  const RtlirVariable* w = FindVar(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->width, 5u);
}

TEST(ClassScopeResolutionElaboration,
     EnumConstantsOfAClassFoldThroughItsScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class D;\n"
      "  enum {T, U = 7} v;\n"
      "  typedef enum {R, S = 11} f_t;\n"
      "  struct {enum {P, Q = 13} f;} s;\n"
      "  enum {V[2] = 17} r;\n"
      "  parameter enum {G, H = 19} L = H;\n"
      "  class N;\n"
      "    enum {A, B = 23} w;\n"
      "  endclass\n"
      "endclass\n"
      "class E;\n"
      "  localparam int K = D::U + 1;\n"
      "endclass\n"
      "module m;\n"
      "  class C;\n"
      "    enum {X, Y = 5} v;\n"
      "  endclass\n"
      "  logic [C::Y-1:0] z;\n"
      "  localparam int K1 = D::U;\n"
      "  localparam int K2 = D::S;\n"
      "  localparam int K3 = D::Q;\n"
      "  localparam int K4 = D::V1;\n"
      "  localparam int K5 = D::H;\n"
      "  localparam int K6 = D::N::B;\n"
      "  localparam int K7 = E::K;\n"
      "  if (1) begin : g\n"
      "    localparam int K8 = D::U;\n"
      "  end\n"
      "  function automatic int f();\n"
      "    localparam int K9 = D::U;\n"
      "    return K9;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  for (auto [name, value] :
       std::initializer_list<std::pair<const char*, int64_t>>{{"K1", 7},
                                                              {"K2", 11},
                                                              {"K3", 13},
                                                              {"K4", 18},
                                                              {"K5", 19},
                                                              {"K6", 23},
                                                              {"K7", 8}}) {
    EXPECT_EQ(ParamValue(design, name), value) << name;
  }
  const auto* z = FindVar(design, "m", "z");
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(z->width, 5u);
}

TEST(ClassScopeResolutionElaboration,
     StaticPropertyThroughItsScopeIsNoConstant) {
  ElabFixture f;
  ElaborateSrc(
      "class D;\n"
      "  enum {T, U} v;\n"
      "  static int s = 7;\n"
      "endclass\n"
      "module m;\n"
      "  parameter int K = D::s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'K' value is not a constant expression",
                            6, "6.20.2"));
}

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInAModuleClassPropertyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class F;\n"
      "  class C;\n"
      "    F::t p;\n"
      "    class D;\n"
      "      F::t q;\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "incomplete forward type 'F' may prefix the "
                              "class scope resolution operator",
                              line, "8.23"))
        << line;
  }
}

}  // namespace
