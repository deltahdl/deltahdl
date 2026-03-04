// §7.10.2.7: Push_back()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserCh513, BuiltInMethod_PushBack) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int q[$];\n"
                      "  initial q.push_back(42);\n"
                      "endmodule"));
}
// --- Test helpers ---
TEST(ParserSection7, QueueMethodPushBack) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial q.push_back(42);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}
// =========================================================================
// §7.10.2: Queue methods
// =========================================================================
TEST(ParserSection7, QueuePushBack) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial q.push_back(42);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

} // namespace
