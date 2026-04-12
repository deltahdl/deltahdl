#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(EventControlParsing, EventControlEdge) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] a;\n"
      "  wire clk;\n"
      "  always @(edge clk) a = ~a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kEdge);
}

TEST(EventControlParsing, EventControlAtIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @clk a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}
TEST(EventControlParsing, EventControlBareSignal) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(data) a = data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
}

TEST(EventControlParsing, EventControlPosedge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a;\n"
      "  initial begin\n"
      "    @(posedge clk) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(EventControlParsing, EventControlNegedge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a;\n"
      "  initial begin\n"
      "    @(negedge clk) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(EventControlParsing, EventControlNullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk);\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

TEST(EventControlParsing, BackToBackEventControls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk);\n"
      "    @(posedge clk);\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kEventControl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kEventControl);
}
TEST(EventControlParsing, NamedEventParenthesized) {
  auto r = Parse(
      "module t;\n"
      "  event ev;\n"
      "  initial @(ev) ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[1];
  auto* stmt = item->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}


TEST(EventControlParsing, PosedgeNullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge done);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(EventControlParsing, BlockWithEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk);\n"
      "    a = 1;\n"
      "    @(posedge clk);\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 4u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kEventControl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kEventControl);
  EXPECT_EQ(body->stmts[3]->kind, StmtKind::kBlockingAssign);
}

TEST(EventControlParsing, NamedEventBareIdentifier) {
  auto r = Parse(
      "module t;\n"
      "  event ev;\n"
      "  initial @ev ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[1];
  auto* stmt = item->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}

TEST(EventControlParsing, EdgeKeywordInProceduralContext) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    @(edge clk) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kEdge);
}

TEST(EventControlParsing, MemberAccessInEventExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(cb.ack) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  ASSERT_NE(stmt->events[0].signal, nullptr);
  EXPECT_EQ(stmt->events[0].signal->kind, ExprKind::kMemberAccess);
}

}  // namespace
