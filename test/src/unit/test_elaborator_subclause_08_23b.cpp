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

// §8.23: from outside a class, `::` reaches its static properties and methods,
// its parameters and its types. A property or method written without `static`
// belongs to an object, which `C::x` and `C::f()` in a module name none of, so
// each is an error, while a static member and a parameter stay reachable.
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

// §8.8's typed constructor call names the constructor through `::` with no
// object, `D::new(4)` building a D for a C handle, so `new` is the one method
// written without `static` that `::` reaches from outside its class.
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

// §8.23: `Cfg::my_type` names the type Cfg declares and no other, so a module
// array typedef sharing the bare name lends x none of its dimensions; adopted,
// x would be a two-element array of one-bit logic, and `x = 5` an assignment
// of an integral value to it.
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

// §8.23 with §11.12: `A::B::C` names the C nested in the B nested in A,
// walked from A, and not the C of a top-level B that the last prefix alone
// would reach. That C derives from Base, so a handle of it fits a Base formal
// and a formal of its own type, while a handle of the top-level B::C, which
// derives from nothing, is reported for either.
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

// §8.23 with §6.20.1: the class scope resolution operator reaches a member of
// a class nested in another, and a class body's parameter is a localparam,
// so `Outer::Inner::N` is a constant a module localparam may be set to. The
// nested class's parameters were recorded under no key and only a name with
// one identifier before `::` was read as one, so A had no value.
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

// The same for classes declared in the module (§8.26), whose parameters are
// registered as the module's items are elaborated: `logic
// [Outer::Inner::N-1:0] v` after the classes is five bits wide.
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

// §8.23: only a chain of class or package names before `::` names a scoped
// parameter, so `a[0].b` has no key even where "a.b" holds one: it neither
// folds to that value nor counts as a constant.
TEST(ClassScopeResolutionElaboration, SelectInAScopedChainHasNoKey) {
  EvalFixture f;
  ScopeMap scope{{"a.b", 3}};
  auto* e = ParseExprFrom("a[0].b", f);
  EXPECT_EQ(ConstEvalInt(e, scope), std::nullopt);
  EXPECT_FALSE(IsConstantExpr(e, scope));
}

// §8.23 with §7.4.4: `Outer::Inner::t` is the typedef of the class Inner
// declared within Outer, never that of the compilation unit's own Inner, so a
// function's return type, its formal and its body's variable written with the
// chain each take the nested class's three elements. Each was looked up by its
// last prefix alone, `Inner::t`, and took the unit Inner's two.
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

// §3.12.1 with §8.23: `$unit::C::t` heads its chain with the compilation unit,
// whose class C's typedef it names, so the formal keeps C's two elements.
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

// The compilation unit's own parameterized `Inner`, whose typedef `t` is ten
// elements longer than the nested class's, and the class `Inner` nested in
// `Outer` with the same parameter.
const char* const kNestedSpecializationClasses =
    "class Inner #(int p = 1);\n"
    "  typedef int t [p + 10];\n"
    "endclass\n"
    "class Outer;\n"
    "  class Inner #(int p = 1);\n"
    "    typedef int t [p];\n"
    "  endclass\n"
    "endclass\n";

// §8.23 with §8.25: `Outer::Inner#(4)::t` specializes the class Inner nested
// in Outer, so a module's variable, a function's return type, its formal and
// its body's variable written so take that class's `[p]` folded with their own
// values. The specialization found its class by the last prefix alone and took
// the unit Inner's `[p + 10]`.
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

// §8.23 with §26.3: `pkg::Inner#(4)::t` specializes the class Inner the
// package pkg declares, whose typedef is twenty elements longer, never the
// unit's Inner, so a module's variable and a function's body variable written
// so each take twenty-four.
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

// A chain whose prefixes reach no class, `Outer::Missing::Inner`, names no
// class to specialize, so the declaration takes none of the unit Inner's
// fourteen elements.
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

// §8.23: `Outer::Inner::s` is the typedef of the class Inner nested in Outer,
// so a module's variable written so is that typedef's eight bits, not the
// compilation unit Inner's four, and `Outer::Inner::u`, which the unit's Inner
// does not declare, is six bits and no error. Both were looked up by their last
// prefix alone, `Inner::s` and `Inner::u`: the first found the unit's
// typedef, and the second nothing, reported as a type the unit's Inner lacks.
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

}  // namespace
