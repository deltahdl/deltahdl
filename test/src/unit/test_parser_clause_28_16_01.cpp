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

// §28.16.1 allows three delay slots (rise, fall, turn-off) for gate
// primitives, and each slot may itself be a min:typ:max triple. A three-state
// gate such as bufif0 exercises the turn-off (third) slot, which the two-slot
// and UDP cases above cannot reach. Mirrors the bufif0 form shown in the
// clause's own example.
TEST(MinTypMaxDelayParsing, GateThreeSlotTurnOffTriple) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, ctrl;\n"
      "  bufif0 #(5:7:9, 8:10:12, 15:18:21) g1(y, a, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleItem* item = nullptr;
  for (auto* it : r.cu->modules[0]->items) {
    if (it->kind == ModuleItemKind::kGateInst) item = it;
  }
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->gate_delay, nullptr);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  ASSERT_NE(item->gate_delay_decay, nullptr);
  EXPECT_EQ(item->gate_delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->gate_delay_fall->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->gate_delay_decay->kind, ExprKind::kMinTypMax);
}

// §28.16.1 requires the min:typ:max form to carry all three colon-separated
// expressions. Once the first colon commits a delay to the triple form, the
// parser requires the second colon and the maximum expression; an incomplete
// "min:typ" without a maximum is rejected.
TEST(MinTypMaxDelayParsing, IncompleteMinTypMaxIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(1:2) y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §28.16.1 extends the min:typ:max delay syntax to gate primitives
// "including UDPs". UDP-instance delays parse through the same delay path as
// gates, so each rise/fall slot may itself be a min:typ:max triple (UDPs are
// limited to two delays per the §29.8 dependency, so no turn-off slot here).
TEST(MinTypMaxDelayParsing, UdpInstanceDelayTriples) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  my_udp #(2:3:4, 5:6:7) u1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleItem* inst = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kUdpInst) inst = item;
  }
  ASSERT_NE(inst, nullptr);
  ASSERT_NE(inst->gate_delay, nullptr);
  ASSERT_NE(inst->gate_delay_fall, nullptr);
  EXPECT_EQ(inst->gate_delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(inst->gate_delay_fall->kind, ExprKind::kMinTypMax);
}

}
