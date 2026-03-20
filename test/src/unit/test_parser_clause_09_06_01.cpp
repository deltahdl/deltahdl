#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProceduralAssignAndControlParsing, WaitForkStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

TEST(ProceduralAssignAndControlParsing, ForkJoinNoneWithWaitFork) {
  auto r = Parse(
      "module m;\n"
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

TEST(ProcessParsing, ForkJoinNoneThenWaitFork) {
  auto r = Parse(
      "module m;\n"
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
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kFork);
  EXPECT_EQ(body->stmts[0]->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

}  // namespace
