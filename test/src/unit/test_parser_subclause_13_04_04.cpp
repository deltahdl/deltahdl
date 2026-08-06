#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(FunctionBackgroundProcessParsing, ForkJoinNoneInFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    fork\n"
      "      $display(\"a\");\n"
      "      $display(\"b\");\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  auto* fork = func->func_body_stmts[0];
  EXPECT_EQ(fork->kind, StmtKind::kFork);
  EXPECT_EQ(fork->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(fork->fork_stmts.size(), 2u);
}

TEST(FunctionBackgroundProcessParsing, ForkJoinInFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  auto* fork = func->func_body_stmts[0];
  EXPECT_EQ(fork->kind, StmtKind::kFork);
  EXPECT_EQ(fork->join_kind, TokenKind::kKwJoin);
}

}  // namespace
