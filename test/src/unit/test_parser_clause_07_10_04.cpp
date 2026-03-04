// §7.10.4: Updating a queue using assignment and unpacked array concatenation

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
// --- Test helpers ---
namespace {

// =========================================================================
// §7.10.4: Empty concatenation {} to clear queue
// =========================================================================
TEST(ParserSection7, EmptyConcatClearQueue_Parse) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}
// =========================================================================
// §7.10.1: Queue operators
// =========================================================================
TEST(ParserSection7, QueueConcatAssign) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

}  // namespace
