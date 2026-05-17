#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(MinTypMaxDelayParsing, GateDelaySingleSlot) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire a, b, c;\n"
              "  and #(2:3:4) g1(c, a, b);\n"
              "endmodule\n"));
}

TEST(MinTypMaxDelayParsing, ContAssignTripleFields) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(10:20:30) y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* delay = r.cu->modules[0]->items[2]->assign_delay;
  ASSERT_NE(delay, nullptr);
  ASSERT_EQ(delay->kind, ExprKind::kMinTypMax);
  ASSERT_NE(delay->lhs, nullptr);
  ASSERT_NE(delay->condition, nullptr);
  ASSERT_NE(delay->rhs, nullptr);
  EXPECT_EQ(delay->lhs->int_val, 10u);
  EXPECT_EQ(delay->condition->int_val, 20u);
  EXPECT_EQ(delay->rhs->int_val, 30u);
}

TEST(MinTypMaxDelayParsing, ArithmeticSubExpressions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire y, a;\n"
              "  assign #(1+2 : 3+4 : 5+6) y = a;\n"
              "endmodule\n"));
}

TEST(MinTypMaxDelayParsing, GateDelayTwoSlots) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b, c;\n"
              "  and #(1:2:3, 4:5:6) g1(c, a, b);\n"
              "endmodule\n"));
}

TEST(MinTypMaxDelayParsing, ProceduralDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #(1:2:3) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_EQ(stmt->delay->kind, ExprKind::kMinTypMax);
}

TEST(MinTypMaxDelayParsing, NetDelaySingleSlot) {
  auto r = Parse(
      "module m;\n"
      "  wire #(1:2:3) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kMinTypMax);
}

TEST(MinTypMaxDelayParsing, NetDelayThreeSlotTriples) {
  auto r = Parse(
      "module m;\n"
      "  wire #(1:2:3, 4:5:6, 7:8:9) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  ASSERT_NE(item->net_delay_fall, nullptr);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->net_delay_fall->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->net_delay_decay->kind, ExprKind::kMinTypMax);
}

TEST(MinTypMaxDelayParsing, ContAssignDelayTwoSlotTriples) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(1:2:3, 4:5:6) y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  ASSERT_NE(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->assign_delay_fall->kind, ExprKind::kMinTypMax);
}

TEST(MinTypMaxDelayParsing, MinExceedsTypAndMaxAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(10:5:3) y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* delay = r.cu->modules[0]->items[2]->assign_delay;
  ASSERT_NE(delay, nullptr);
  ASSERT_EQ(delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(delay->lhs->int_val, 10u);
  EXPECT_EQ(delay->condition->int_val, 5u);
  EXPECT_EQ(delay->rhs->int_val, 3u);
}

TEST(MinTypMaxDelayParsing, IdentifierExpressionsInTriple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter min_hi = 95, typ_hi = 100, max_hi = 105;\n"
              "  wire y, a;\n"
              "  assign #(min_hi : typ_hi : max_hi) y = a;\n"
              "endmodule\n"));
}

}
