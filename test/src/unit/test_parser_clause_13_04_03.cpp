#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ConstantFunctionParsing, CallInParameterPort) {
  auto r = Parse(
      "module m #(parameter int P = calc(4));\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  ASSERT_NE(params[0].second, nullptr);
  EXPECT_EQ(params[0].second->kind, ExprKind::kCall);
  EXPECT_EQ(params[0].second->callee, "calc");
}

TEST(ConstantFunctionParsing, CallInLocalparam) {
  auto r = Parse(
      "module m;\n"
      "  function int clog2_fn(int n); return $clog2(n); endfunction\n"
      "  localparam int W = clog2_fn(256);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstantFunctionParsing, CallInParameterDecl) {
  auto r = Parse(
      "module m;\n"
      "  function int eight(); return 8; endfunction\n"
      "  parameter P = eight();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstantFunctionParsing, CallInSubExpression) {
  auto r = Parse(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  localparam int P = calc(4) + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
