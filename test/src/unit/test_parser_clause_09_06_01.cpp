// §9.6.1: Wait fork statement

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =============================================================================
// Section 9.7 -- Fine-grain process control
// =============================================================================
TEST(ParserSection9b, WaitForkStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      #10 a = 1;\n"
                 "    join_none\n"
                 "    wait fork;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

TEST(ParserSection9b, ForkJoinNoneWithWaitFork) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      begin #10 a = 1; end\n"
                 "      begin #20 b = 1; end\n"
                 "    join_none\n"
                 "    wait fork;\n"
                 "    $display(\"all done\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
// ---------------------------------------------------------------------------
// 17. Fork-join_none followed by wait fork
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_ForkJoinNoneThenWaitFork) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      begin #10 a = 1; end\n"
                 "      begin #20 b = 2; end\n"
                 "    join_none\n"
                 "    wait fork;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kFork);
  EXPECT_EQ(body->stmts[0]->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

// §9.6.1: wait fork
TEST(ParserA605, WaitFork) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait fork;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitFork);
}

} // namespace
