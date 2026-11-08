#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(EventTriggerParser, BlockingTrigger) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(EventTriggerParser, NonblockingTrigger) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(EventTriggerParser, NonblockingHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial ->> top.e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
}

TEST(EventTriggerParser, NonblockingWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> #5 ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(EventTriggerParser, NonblockingWithParenDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> #(10) ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(EventTriggerParser, NonblockingNoDelayHasNullDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_EQ(stmt->delay, nullptr);
}

TEST(EventTriggerParser, NonblockingWithEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> @(posedge clk) ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

TEST(EventTriggerParser, NonblockingWithRepeatEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> repeat(2) @(posedge clk) ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

TEST(EventTriggerParser, BlockingTriggerArraySelect) {
  auto r = Parse(
      "module m;\n"
      "  event ev [4];\n"
      "  initial begin\n"
      "    -> ev[2];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSelect);
}

TEST(EventTriggerParser, NonblockingTriggerArraySelect) {
  auto r = Parse(
      "module m;\n"
      "  event ev [4];\n"
      "  initial begin\n"
      "    ->> ev[1];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSelect);
}

TEST(EventTriggerParser, BlockingHierarchical) {
  auto r = Parse(
      "module m;\n"
      "  initial -> top.e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
}

TEST(EventTriggerParser, BlockingTriggerRejectsDelay) {
  auto r = Parse(
      "module m;\n"
      "  event ev;\n"
      "  initial -> #5 ev;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(EventTriggerParser, PosedgeInIfConditionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  initial if (posedge clk) ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

}  // namespace
