#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(TaskAndFunctionParsing, ScopeCallParsesAsExpr) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] d;\n"
      "  logic [2:0] e;\n"
      "  assign e = Codec#(8)::encode(d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TaskAndFunctionParsing, TwoSpecializations) {
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

TEST(TaskAndFunctionParsing, MultiParamSpecialization) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [31:0] result;\n"
      "  assign result = Xform#(16, 32, 2)::widen(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TaskAndFunctionParsing, TypeParamOverrideCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] x, y;\n"
              "  assign y = Converter#(logic [7:0])::identity(x);\n"
              "endmodule\n"));
}

TEST(TaskAndFunctionParsing, ChainedParameterizedCalls) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a, b, c;\n"
              "  assign c = Arith#(8)::add(a, Arith#(8)::add(a, b));\n"
              "endmodule\n"));
}

TEST(TaskAndFunctionParsing, ExplicitParamSpecialization) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [31:0] d, r;\n"
              "  assign r = Shifter#(4)::left(d);\n"
              "endmodule\n"));
}

TEST(TaskAndFunctionParsing, CallParamTaskFromInitial) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial Utils#(16)::report();\n"
              "endmodule\n"));
}

TEST(TaskAndFunctionParsing, ParamCallInTernary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] x, y;\n"
              "  logic sel;\n"
              "  assign y = sel ? C#(8)::ENCODER_f(x) : '0;\n"
              "endmodule\n"));
}

TEST(ClassParsing, ParameterizedClassScopeResolution) {
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

}  // namespace
