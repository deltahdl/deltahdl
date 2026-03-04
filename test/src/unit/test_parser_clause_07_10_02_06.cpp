// §7.10.2.6: Push_front()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
// --- Test helpers ---
namespace {

TEST(ParserSection7, QueuePushFront) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q.push_front(99);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

}  // namespace
