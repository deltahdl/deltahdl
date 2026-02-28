// Annex D.6: $list

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexD, AnnexDList) {
  auto r = Parse("module m; initial $list; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

}  // namespace
