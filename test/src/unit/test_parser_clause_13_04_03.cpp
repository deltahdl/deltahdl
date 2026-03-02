// §13.4.3: Constant functions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.2 Subroutine calls — constant_function_call
// =============================================================================
// § constant_function_call ::= function_subroutine_call (footnote 41)
TEST(ParserA82, ConstantFunctionCallInParam) {
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

TEST(ParserA82, ConstantFunctionCallInLocalparam) {
  auto r = Parse(
      "module m;\n"
      "  function int clog2_fn(int n); return $clog2(n); endfunction\n"
      "  localparam int W = clog2_fn(256);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
