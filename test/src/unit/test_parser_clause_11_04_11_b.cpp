// §11.4.11: Conditional operator

#include "fixture_parser.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/eval.h"
#include "simulator/udp_eval.h"

using namespace delta;
namespace {

TEST(ParserCh505, Operator_Ternary) {
  auto r = Parse(
      "module m;\n"
      "  initial x = sel ? a : b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  ASSERT_NE(rhs->true_expr, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
}

TEST(Eval, Ternary) {
  ExprFixture f;
  auto* expr = ParseExprFrom("1 ? 42 : 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}
// =========================================================================
// Section 11.4.11 -- Conditional operator
// =========================================================================
TEST(ParserSection11, ConditionalTernary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > b) ? a : b;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
}  // namespace
