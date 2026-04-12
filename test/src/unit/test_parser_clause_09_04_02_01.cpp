#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(EventOrOperatorParsing, EventControlMultipleOrExpressions) {
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

TEST(EventOrOperatorParsing, EventControlMixedEdgesComma) {
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

TEST(EventOrOperatorParsing, OrInAlwaysSensitivityList) {
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

TEST(EventOrOperatorParsing, OrWithNamedEvents) {
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
TEST(EventOrOperatorParsing, OrWithEdgeQualifiedSignals) {
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

TEST(EventOrOperatorParsing, EventControlComma) {
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

TEST(EventOrOperatorParsing, EventExprMixedOrComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(a or b, c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 3u);
}

TEST(EventOrOperatorParsing, EventExprMultipleEdgesOrComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge a or negedge b, edge c or d) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 4u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kEdge);
  EXPECT_EQ(stmt->events[3].edge, Edge::kNone);
}

TEST(EventOrOperatorParsing, ParenthesizedOrGroupWithComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @((posedge a or negedge b), c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 3u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kNone);
}

TEST(EventOrOperatorParsing, FiveSignalCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  always @(a, b, c, d, e) x = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 5u);
  for (size_t i = 0; i < 5; ++i) {
    EXPECT_EQ(item->sensitivity[i].edge, Edge::kNone) << "event " << i;
  }
}

TEST(EventOrOperatorParsing, InterleavedOrGroupsWithComma) {
  auto r = Parse(
      "module m;\n"
      "  always @(a or b, c, d or e) x = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 5u);
}

}  // namespace
