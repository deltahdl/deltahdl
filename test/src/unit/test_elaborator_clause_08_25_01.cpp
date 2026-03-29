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

TEST(ParameterizedScopeResolutionElaboration, ExplicitDefaultAccessesLocalParamOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  initial result = C#()::q;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration, ExplicitDefaultAccessesClassParamOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  initial result = C#()::p;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration, SpecificSpecializationAccessesParamOk) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  initial result = C#(10)::p;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration, BothClassAndLocalParamsAccessibleOk) {
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

TEST(ParameterizedScopeResolutionElaboration, OutOfBlockMethodForParameterizedClassOk) {
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

TEST(ParameterizedScopeResolutionElaboration, UnadornedScopeInContAssignIsError) {
  EXPECT_FALSE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  assign result = C::q;\n"
             "endmodule\n"));
}

TEST(ParameterizedScopeResolutionElaboration, ExplicitDefaultIsNotError) {
  EXPECT_TRUE(
      ElabOk("class C #(int p = 1);\n"
             "  parameter int q = 5;\n"
             "endclass\n"
             "module m;\n"
             "  int result;\n"
             "  initial result = C#()::q;\n"
             "endmodule\n"));
}

}  // namespace
