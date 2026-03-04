// §7.6: Array assignments

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =========================================================================
// §7.4.6: Operations on arrays
// =========================================================================
TEST(ParserSection7, ArrayAssignWhole) {
  auto r = Parse("module t;\n"
                 "  int a[4], b[4];\n"
                 "  initial a = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// =========================================================================
// §7.6: Array assignments
// =========================================================================
TEST(ParserSection7, ArraySliceAssign) {
  auto r = Parse("module t;\n"
                 "  int a[8], b[8];\n"
                 "  initial a[3:0] = b[7:4];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

} // namespace
