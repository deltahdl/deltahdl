#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OptionalSystemTaskParserParsing, Countdrivers) {
  auto r = Parse("module m; initial $countdrivers(sig); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

// Annex D.2: the call template carries an optional trailing argument list (the
// net followed by up to five output arguments), so the argument count may vary.
// The full six-argument form parses as one system call retaining every argument.
TEST(OptionalSystemTaskParserParsing, CountdriversOptionalArguments) {
  auto r = Parse(
      "module m;\n"
      "  initial $countdrivers(sig, f, n01x, n0, n1, nx);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$countdrivers");
  EXPECT_EQ(stmt->expr->args.size(), 6u);
}

}
