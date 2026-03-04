// §15.5.4: Event sequencing: wait_order()

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §15.5.4: action_block in wait_order statement
TEST(ParserA603, ActionBlockWaitOrder) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order (a, b, c) $display(\"ok\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
}

// §15.5.4: action_block in wait_order with else clause
TEST(ParserA603, ActionBlockWaitOrderElse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order (a, b) else $display(\"out of order\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
}

// --- Test helpers ---
// =============================================================================
// §15.5.4 — wait_order basic parsing
// =============================================================================
TEST(ParserSection15, WaitOrderBasic) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b, c);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
  const std::string kExpected[] = {"a", "b", "c"};
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(stmt->wait_order_events[i]->text, kExpected[i]);
  }
}

// =============================================================================
// §15.5.4 — wait_order with else clause
// =============================================================================
TEST(ParserSection15, WaitOrderWithElseKind) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b, c) success = 1;\n"
                 "    else success = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
}

TEST(ParserSection15, WaitOrderWithElseBranches) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b, c) success = 1;\n"
                 "    else success = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
}

// =============================================================================
// §15.5.4 — wait_order with two events
// =============================================================================
TEST(ParserSection15, WaitOrderTwoEvents) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(ev1, ev2);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 2u);
}

// =============================================================================
// §15.5.4 — wait_order null action (just semicolon)
// =============================================================================
TEST(ParserSection15, WaitOrderNullAction) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b, c);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  // Null action: then_branch is null or a null stmt.
}

// §15.5.4: wait_order with semicolon (null action)
TEST(ParserA605, WaitOrderNull) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b, c);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
}

// §15.5.4: wait_order with success statement
TEST(ParserA605, WaitOrderWithAction) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b) success = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->then_branch, nullptr);
}

// §15.5.4: wait_order with else clause
TEST(ParserA605, WaitOrderWithElse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b, c) success = 1;\n"
                 "    else success = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// §15.5.4: wait_order with only else clause
TEST(ParserA605, WaitOrderElseOnly) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b)\n"
                 "    else x = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->else_branch, nullptr);
}

} // namespace
