#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProcessTimingAndControlParsing, EventControlMultipleOrExpressions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(a or b or c) x = a + b + c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_GE(stmt->events.size(), 3u);
}

TEST(ProcessTimingAndControlParsing, EventControlMixedEdgesComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk, negedge rst, a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_GE(stmt->events.size(), 3u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kNone);
}

TEST(SchedulingSemanticsParsing, MultipleEventControlInAlways) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, rst, a;\n"
      "  always @(posedge clk or negedge rst) begin\n"
      "    if (!rst)\n"
      "      a <= 0;\n"
      "    else\n"
      "      a <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
}

TEST(InterprocessSyncParsing, WaitForEventOrExpr) {
  auto r = Parse(
      "module m;\n"
      "  event e1, e2;\n"
      "  initial begin\n"
      "    @(e1 or e2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_GE(stmt->events.size(), 2u);
}
TEST(ProcessParsing, EventControlMultiple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk or negedge rst) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_GE(stmt->events.size(), 2u);
  const Edge kExpectedEdges[] = {Edge::kPosedge, Edge::kNegedge};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(stmt->events[i].edge, kExpectedEdges[i]);
  }
}

TEST(ProcessParsing, EventControlComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk, negedge rst) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_GE(stmt->events.size(), 2u);
}

}  // namespace
