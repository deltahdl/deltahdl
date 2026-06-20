#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParameterizedScopeResolutionElaboration, ValueParamScopeOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     ExplicitDefaultAccessesLocalParamOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  initial result = C#()::q;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     ExplicitDefaultAccessesClassParamOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  initial result = C#()::p;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     SpecificSpecializationAccessesParamOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  initial result = C#(10)::p;\n"
             "endmodule\n"));
}

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

TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeOutsideIsError) {
  EXPECT_FALSE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  initial result = C::q;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInContAssignIsError) {
  EXPECT_FALSE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  assign result = C::q;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInNestedExprIsError) {
  // The prohibition on the bare parameterized-class name as a scope resolution
  // prefix outside the class applies wherever the prefix appears, including as
  // a subexpression of a larger expression, not only as the whole right-hand
  // side.
  EXPECT_FALSE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  initial result = 1 + C::q;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration,
     UnadornedScopeInAlwaysCombIsError) {
  // The same prohibition holds across procedural contexts; an always_comb block
  // outside the class is still outside the class, so the unadorned prefix is
  // illegal there too.
  EXPECT_FALSE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  always_comb result = C::q;\n"
             "endmodule\n"));
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

}  // namespace
