#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AggregateTypeParsing, QueuePushBack) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.push_back(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

// The push_back() prototype takes a single input item argument. Observe that
// the parser names the method push_back on the queue and carries exactly one
// argument expression for the pushed item.
TEST(AggregateTypeParsing, QueuePushBackItemArgument) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.push_back(42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  ASSERT_EQ(expr->kind, ExprKind::kCall);

  auto* callee = expr->lhs;
  ASSERT_NE(callee, nullptr);
  EXPECT_EQ(callee->kind, ExprKind::kMemberAccess);
  ASSERT_NE(callee->rhs, nullptr);
  EXPECT_EQ(callee->rhs->text, "push_back");

  ASSERT_EQ(expr->args.size(), 1u);
}

}
