#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(WaitOrderParser, WaitOrderBasic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
  const std::string kExpected[] = {"a", "b", "c"};
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(stmt->wait_order_events[i]->text, kExpected[i]);
  }
}

// Syntax 15-2's operand list is `hierarchical_identifier { ,
// hierarchical_identifier }`: the trailing comma group may repeat zero times,
// so a single operand is the minimal legal form. Exercise that base case at the
// parse stage.
TEST(WaitOrderParser, WaitOrderSingleEvent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 1u);
  EXPECT_EQ(stmt->wait_order_events[0]->text, "a");
}

TEST(WaitOrderParser, WaitOrderTwoEvents) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(ev1, ev2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 2u);
}

// Syntax 15-2 names each operand a hierarchical_identifier, so a dotted
// (hierarchical) name is an admitted operand form, not just a bare identifier.
// The operand should parse into a member-access expression in the event list.
TEST(WaitOrderParser, WaitOrderHierarchicalOperand) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(blk.ev, c);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 2u);
  EXPECT_EQ(stmt->wait_order_events[0]->kind, ExprKind::kMemberAccess);
}

TEST(WaitOrderParser, WaitOrderWithAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b) success = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->then_branch, nullptr);
}

TEST(WaitOrderParser, WaitOrderWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) success = 1;\n"
      "    else success = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// Syntax 15-2 requires at least one hierarchical_identifier inside the
// parentheses: `wait_order ( hierarchical_identifier { ,
// hierarchical_identifier } )`. An empty operand list has no identifier to
// satisfy the first term, so the parser must reject it.
TEST(WaitOrderParser, WaitOrderEmptyOperandListRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(WaitOrderParser, WaitOrderElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b)\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->else_branch, nullptr);
}

}  // namespace
