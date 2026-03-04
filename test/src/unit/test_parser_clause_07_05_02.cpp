// §7.5.2: Size()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- §5.13 Built-in methods ---
namespace {

// From test_parser_clause_05.cpp
TEST(ParserCh513, BuiltInMethodCall_Parse) {
  auto r = Parse(
      "module t;\n"
      "  initial x = arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(ParserCh513, BuiltInMethodCall_Callee) {
  // The callee_expr should be the full member-access expression.
  auto r = Parse(
      "module t;\n"
      "  initial x = arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
}

// --- Test helpers ---
TEST(ParserSection7c, DynamicArraySize) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    dyn = new[5];\n"
      "    sz = dyn.size();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
// =========================================================================
// §7.5.2/7.5.3: Dynamic array size() and delete()
// =========================================================================
TEST(ParserSection7, DynamicArraySizeMethod) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  initial x = dyn.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

}  // namespace
