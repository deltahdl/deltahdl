#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserCh513, BuiltInMethod_ChainedAccess) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial x = obj.sub.method();\n"
              "endmodule"));
}

TEST(ParserSection11, Sec11_1_MemberAccessExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = obj.field;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, Sec7_2_2_MemberAssignment) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p.a = 10;\n"
      "    p.b = 20;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = NthInitialStmt(r, 0);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection7, StructMemberAccess) {
  auto r = Parse(
      "module t;\n"
      "  struct { int x; int y; } s;\n"
      "  initial s.x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

}
