// §7.10.2.1: Size()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
// --- Test helpers ---
namespace {

TEST(ParserSection7, QueueSizeMethod) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial x = q.size();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(ParserSection7, QueueMethodSize) {
  auto r = Parse("module t;\n"
                 "  int q[$];\n"
                 "  initial y = q.size;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

} // namespace
