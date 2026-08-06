#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(EventTriggeredParser, TriggeredMethodWait) {
  auto r = Parse(
      "module m;\n"
      "  event blast;\n"
      "  initial begin\n"
      "    wait(blast.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(EventTriggeredParser, TriggeredMethodForkPattern) {
  auto r = Parse(
      "module m;\n"
      "  event blast;\n"
      "  initial begin\n"
      "    fork\n"
      "      -> blast;\n"
      "      wait(blast.triggered);\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kEventTrigger);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kWait);
}

TEST(EventTriggeredParser, TriggeredMethodHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait(top.ev.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(EventTriggeredParser, TriggeredMethodEventAlias) {
  auto r = Parse(
      "module m;\n"
      "  event done;\n"
      "  event done_too;\n"
      "  initial begin\n"
      "    fork\n"
      "      @done_too;\n"
      "      #1 -> done;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
}

TEST(EventTriggeredParser, TriggeredMethodCallForm) {
  // §15.5.3: the method prototype carries empty parentheses, so the
  // parenthesized call form ev.triggered() is a legal invocation alongside the
  // bare-member form. The wait condition parses as a call expression (its
  // receiver being the event member access), distinct from the plain member
  // access of ev.triggered.
  auto r = Parse(
      "module m;\n"
      "  event ev;\n"
      "  initial begin\n"
      "    wait(ev.triggered());\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kCall);
}

}  // namespace
