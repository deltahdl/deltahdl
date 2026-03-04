// §11.3.3: Using integer literals in expressions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection11, LiteralAsExpression) {
  auto r = Parse("module t;\n"
                 "  initial x = 42;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// =============================================================================
// A.8.3 Expressions — expression
// =============================================================================
// § expression ::= primary
TEST(ParserA83, ExprPrimary) {
  auto r = Parse("module m; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

} // namespace
