// §7.10.2.5: Pop_back()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
// --- Test helpers ---
namespace {

TEST(ParserSection7, QueuePopBack) {
  auto r = Parse("module t;\n"
                 "  int q[$] = '{1, 2, 3};\n"
                 "  initial y = q.pop_back();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

} // namespace
