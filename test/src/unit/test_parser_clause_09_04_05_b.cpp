#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ProcessParsing, RepeatEventSignalField) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(2) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  ASSERT_NE(stmt->events[0].signal, nullptr);
  EXPECT_EQ(stmt->events[0].signal->text, "clk");
}

TEST(ProcessParsing, ParseOkRepeatEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg clk, a, b;\n"
              "  initial begin\n"
              "    a = repeat(10) @(posedge clk) b;\n"
              "    a <= repeat(5) @(negedge clk) b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ProcessParsing, IntraDelayNoEventsField) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial a = #10 b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_TRUE(stmt->events.empty());
  EXPECT_EQ(stmt->repeat_event_count, nullptr);
}

TEST(ProceduralAssignAndControlParsing, NonblockingAssignWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial q <= #5 d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(ProceduralAssignAndControlParsing, NonblockingAssignWithEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial a <= @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

TEST(ProcessParsing, RepeatEventControl) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(3) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

TEST(ProceduralBlockSyntaxParsing, BlockingAssignment_WithIntraDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = #10 b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(AssignmentParsing, IntraAssignEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = @(posedge clk) b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->events.empty());
  ASSERT_NE(stmt->rhs, nullptr);
}

}  // namespace
