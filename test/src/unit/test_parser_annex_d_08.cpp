#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OptionalSystemTaskExtendedParsing, ResetFamily) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $reset;\n"
      "    x = $reset_count;\n"
      "    y = $reset_value;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// Annex D.8: $reset accepts an optional argument list carrying stop_value,
// reset_value, and diagnostics_value. Observe that the full three-argument
// form parses into a system call with all three operands attached.
TEST(OptionalSystemTaskExtendedParsing, ResetWithArguments) {
  auto r = Parse("module m; initial $reset(1, 42, 3); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$reset");
  ASSERT_EQ(stmt->expr->args.size(), 3u);
}

// Annex D.8: the argument list is nested-optional, so a $reset call may supply
// stop_value alone. Observe that the single-argument form parses.
TEST(OptionalSystemTaskExtendedParsing, ResetWithStopValueOnly) {
  auto r = Parse("module m; initial $reset(1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$reset");
  ASSERT_EQ(stmt->expr->args.size(), 1u);
}

// Annex D.8: stop_value and reset_value may be supplied without
// diagnostics_value. Observe that the two-argument form parses.
TEST(OptionalSystemTaskExtendedParsing, ResetWithStopAndResetValue) {
  auto r = Parse("module m; initial $reset(1, 42); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$reset");
  ASSERT_EQ(stmt->expr->args.size(), 2u);
}

}  // namespace
