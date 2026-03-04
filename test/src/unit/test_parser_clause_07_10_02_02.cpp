// §7.10.2.2: and 7.10.2.3) at the back (i.e., right side) of the queue as
// necessary to produce the new

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
// --- Test helpers ---
namespace {

TEST(ParserSection7, QueueInsertMethod) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.insert(2, 99);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

}  // namespace
