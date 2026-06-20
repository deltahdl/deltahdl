#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// Syntax 20-16: a PLA modeling system task parses as a system call whose callee
// is the full $array_type$logic$format name and whose three arguments are the
// memory identifier, the input terms, and the output terms.
TEST(PlaSystemTask, ParsesAsSystemCallWithThreeArguments) {
  auto r = Parse(
      "module m; initial $async$and$array(mem, {a1, a2}, {b1, b2}); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$async$and$array");
  ASSERT_EQ(stmt->expr->args.size(), 3u);
}

// Syntax 20-16: memory_identifier is a plain identifier and the input/output
// terms may be single expressions rather than concatenations.
TEST(PlaSystemTask, ParsesSingleTermArguments) {
  auto r = Parse("module m; initial $sync$or$plane(mem, ai, bo); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$sync$or$plane");
  ASSERT_EQ(stmt->expr->args.size(), 3u);
  ASSERT_NE(stmt->expr->args[0], nullptr);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->expr->args[0]->text, "mem");
}

}  // namespace
