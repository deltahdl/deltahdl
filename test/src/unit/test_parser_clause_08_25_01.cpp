#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParameterizedScopeResolutionParsing, ScopeCallParsesAsExpr) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] d;\n"
      "  logic [2:0] e;\n"
      "  assign e = Codec#(8)::encode(d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterizedScopeResolutionParsing, TwoSpecializations) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a4;\n"
      "  logic [15:0] a16;\n"
      "  logic [1:0] r4;\n"
      "  logic [3:0] r16;\n"
      "  assign r4  = C#(4)::ENCODER_f(a4);\n"
      "  assign r16 = C#(16)::ENCODER_f(a16);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterizedScopeResolutionParsing, MultiParamSpecialization) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [31:0] result;\n"
      "  assign result = Xform#(16, 32, 2)::widen(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterizedScopeResolutionParsing, TypeParamOverrideCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] x, y;\n"
              "  assign y = Converter#(logic [7:0])::identity(x);\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, ChainedParameterizedCalls) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a, b, c;\n"
              "  assign c = Arith#(8)::add(a, Arith#(8)::add(a, b));\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, CallParamTaskFromInitial) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial Utils#(16)::report();\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, ParamCallInTernary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] x, y;\n"
              "  logic sel;\n"
              "  assign y = sel ? C#(8)::ENCODER_f(x) : '0;\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, ExplicitDefaultAccessesLocalParam) {
  auto r = Parse(
      "module m;\n"
      "  class par_cls #(parameter int a = 25);\n"
      "    parameter int b = 23;\n"
      "  endclass\n"
      "  initial begin\n"
      "    $display(par_cls#()::b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParameterizedScopeResolutionParsing, ExplicitDefaultAccessesClassParam) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class C #(parameter int p = 1);\n"
              "  endclass\n"
              "  int result;\n"
              "  initial result = C#()::p;\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, ExplicitSpecAccessesClassParam) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class C #(parameter int p = 1);\n"
              "  endclass\n"
              "  int result;\n"
              "  initial result = C#(5)::p;\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, OutOfBlockMethodForParameterizedClass) {
  EXPECT_TRUE(
      ParseOk("class C #(int p = 1);\n"
              "  extern static function int f();\n"
              "endclass\n"
              "function int C::f();\n"
              "  return p;\n"
              "endfunction\n"
              "module m;\n"
              "endmodule\n"));
}

TEST(ParameterizedScopeResolutionParsing, EmptyParamListWithMemberAccess) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class C #(parameter int p = 10);\n"
              "    parameter int q = 20;\n"
              "  endclass\n"
              "  int a, b;\n"
              "  initial begin\n"
              "    a = C#()::p;\n"
              "    b = C#()::q;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
