#include <gtest/gtest.h>

#include <cstddef>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

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

TEST(WaitOrderParser, WaitOrderEmptyOperandListRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
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

TEST(WaitOrderParser, APackageQualifiedOperandIsReported) {
  auto r = Parse(
      "package pk;\n"
      "  event pe;\n"
      "endpackage\n"
      "module m;\n"
      "  event a;\n"
      "  initial begin\n"
      "    wait_order(a, pk::pe);\n"
      "    wait_order(a, $root.m.a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "wait_order operand shall be a hierarchical identifier", 7,
      "15.5.4"));
  EXPECT_EQ(r.diags.size(), 1u);
}

}  // namespace
