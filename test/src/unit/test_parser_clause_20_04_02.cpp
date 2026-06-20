#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Syntax 20-4: the parens block is optional, so a bare $printtimescale is
// parsed as an expression statement wrapping an argument-less system call.
TEST(PrinttimescaleSysTask, BareInvocationParsesAsArglessSystemCall) {
  auto r = Parse("module m; initial $printtimescale; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$printtimescale");
  EXPECT_TRUE(stmt->expr->args.empty());
}

// Syntax 20-4: the optional argument is a hierarchical identifier naming the
// design element whose timescale is reported.
TEST(PrinttimescaleSysTask, HierarchicalArgumentParses) {
  auto r = Parse("module m; initial $printtimescale(top.dut); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$printtimescale");
  ASSERT_EQ(stmt->expr->args.size(), 1u);
}

}  // namespace
