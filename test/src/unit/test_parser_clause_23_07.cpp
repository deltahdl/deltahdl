// §23.7: Member selects and hierarchical names

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserCh513, BuiltInMethod_ChainedAccess) {
  // Chained member accesses: a.b.c().
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial x = obj.sub.method();\n"
                      "endmodule"));
}
// --- Member access ---
TEST(ParserSection11, Sec11_1_MemberAccessExpression) {
  auto r = Parse("module t;\n"
                 "  initial x = obj.field;\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}
static Stmt *NthInitialStmt(ParseResult &r, size_t n) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        if (item->body->stmts.size() > n)
          return item->body->stmts[n];
      }
      if (n == 0)
        return item->body;
    }
  }
  return nullptr;
}

// 6. Struct member assigned individually (s.a = 1).
TEST(ParserSection7, Sec7_2_2_MemberAssignment) {
  auto r = Parse("module t;\n"
                 "  typedef struct { int a; int b; } pair_t;\n"
                 "  pair_t p;\n"
                 "  initial begin\n"
                 "    p.a = 10;\n"
                 "    p.b = 20;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = NthInitialStmt(r, 0);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}
// --- Test helpers ---
TEST(ParserSection7, StructMemberAccess) {
  auto r = Parse("module t;\n"
                 "  struct { int x; int y; } s;\n"
                 "  initial s.x = 42;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

} // namespace
