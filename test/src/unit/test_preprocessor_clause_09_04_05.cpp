#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(IntraAssignTimingPreprocessing, BlockingIntraAssignDelayKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a = #10 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(IntraAssignTimingPreprocessing, BlockingIntraAssignDelayOperands) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a = #10 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingPreprocessing, NonblockingIntraAssignDelayKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a <= #5 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(IntraAssignTimingPreprocessing, NonblockingIntraAssignDelayOperands) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    a <= #5 b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingPreprocessing, BlockingIntraAssignEventKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingPreprocessing, BlockingIntraAssignEventEdge) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(IntraAssignTimingPreprocessing, NonblockingIntraAssignEventKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a <= @(negedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingPreprocessing, NonblockingIntraAssignEventEdge) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg a, b, clk;\n"
      "  initial begin\n"
      "    a <= @(negedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
}

TEST(IntraAssignTimingPreprocessing, BlockingRepeatEventKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial begin\n"
      "    a = repeat(3) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(IntraAssignTimingPreprocessing, BlockingRepeatEventOperands) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial begin\n"
      "    a = repeat(3) @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(IntraAssignTimingPreprocessing, NonblockingRepeatEventKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg clk, q, d;\n"
      "  initial begin\n"
      "    q <= repeat(5) @(posedge clk) d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(IntraAssignTimingPreprocessing, NonblockingRepeatEventOperands) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  reg clk, q, d;\n"
      "  initial begin\n"
      "    q <= repeat(5) @(posedge clk) d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

}  // namespace
