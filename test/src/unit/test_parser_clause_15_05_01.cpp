#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

TEST(EventTriggerParser, NonblockingWithDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    ->> e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
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

TEST(EventTriggerParser, BlockingWithDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  event e;\n"
      "  initial begin\n"
      "    -> e;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
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

}  // namespace
