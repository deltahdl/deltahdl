// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA82, RandomizeCallWithVarList) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(x, y); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § std::randomize_call (subroutine_call alternative)
TEST(ParserA82, StdRandomizeCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin std::randomize(x) with { x > 0; }; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.2 Subroutine calls — variable_identifier_list / identifier_list
// =============================================================================
// § variable_identifier_list ::= variable_identifier { , variable_identifier }
// § identifier_list ::= identifier { , identifier }
// Tested implicitly via randomize_call with var list above.
// variable_identifier_list in randomize
TEST(ParserA82, VariableIdentifierList) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(a, b, c); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

}  // namespace
