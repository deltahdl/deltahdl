#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingControlSyntaxParsing, DisableFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisableFork);
}
TEST(ProcessParsing, DisableForkAfterJoinNone) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #100;\n"
      "    join_none\n"
      "    #50;\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kDisableFork);
}

TEST(ProceduralAssignAndControlParsing, DisableForkStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "      #20 b = 1;\n"
      "    join_any\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisableFork);
}

TEST(ProceduralAssignAndControlParsing, ForkJoinAnyWithDisableFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      @(posedge clk) a = 1;\n"
      "      #100 a = 0;\n"
      "    join_any\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  auto* fork_stmt = body->stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(DisableForkParsing, DisableForkMissingSemicolon) {
  EXPECT_TRUE(Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable fork\n"
      "  end\n"
      "endmodule\n").has_errors);
}

}  // namespace
