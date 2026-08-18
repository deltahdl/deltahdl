#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ParameterizedScopeResolutionElaboration,
     SpecificSpecializationAccessesTypeParamOk) {
  // The scope resolution operator reaches a type parameter of the class, not
  // only its value parameters. The explicit specialization supplies the actual
  // type that the parameter name resolves to, here giving the variable the
  // integer type.
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

// The report stands at the unadorned prefix itself -- the site passes
// `e->lhs->range.start`, the `C` of `C::q`.
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
  // The prohibition on the bare parameterized-class name as a scope resolution
  // prefix outside the class applies wherever the prefix appears, including as
  // a subexpression of a larger expression, not only as the whole right-hand
  // side.
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
  // The same prohibition holds across procedural contexts; an always_comb block
  // outside the class is still outside the class, so the unadorned prefix is
  // illegal there too.
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
  // Within the parameterized class's own scope the unadorned name may prefix
  // the scope resolution operator to name a member; the restriction that makes
  // the bare name illegal applies only outside the class and its out-of-block
  // declarations. Here it names a member rather than the default
  // specialization.
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

// §8.25.1: the explicit specialization form denotes a specific parameter in a
// constant-expression position, so `C#(4)::p` initializing a localparam folds
// to 4 and not to the class default of 1. §27.4 makes a generate block "a
// separate scope and a new level of hierarchy when it is instantiated" and
// says nothing that would stop that at the boundary, so the same initializer
// written inside a block folds to the same 4. The class default is written 1
// so that a fold answering the default misses.
//
// This fails while Elaborator::ProcessPendingGenerate in
// src/elaborator/elaborator_generate.cpp opens no ParamClassRegistryGuard:
// SpecializedParamClass in src/elaborator/const_eval_func.cpp finds no
// registry, the access does not fold at all, and W is left unresolved.
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

}  // namespace
