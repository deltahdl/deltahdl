#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §28.16.1 R1: a gate-instance delay in min:typ:max form must parse — the
// three colon-separated sub-expressions fill the single rise slot so the
// gate_delay surfaces an ExprKind::kMinTypMax node to downstream passes.
TEST(MinTypMaxDelayParsing, GateDelaySingleSlot) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire a, b, c;\n"
              "  and #(2:3:4) g1(c, a, b);\n"
              "endmodule\n"));
}

// §28.16.1 R1: the three colon-separated sub-expressions of a cont-assign
// mintypmax must land in the AST's lhs/condition/rhs so later passes can
// read each branch independently under a DelayMode selection.
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

// §28.16.1 R1: each of the three slots is a full expression, not just an
// integer literal — the parser must accept arithmetic in any position.
TEST(MinTypMaxDelayParsing, ArithmeticSubExpressions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire y, a;\n"
              "  assign #(1+2 : 3+4 : 5+6) y = a;\n"
              "endmodule\n"));
}

// §28.16.1 R1: in a multi-delay spec (here, delay2) each comma-separated
// position independently accepts a full mintypmax triple.
TEST(MinTypMaxDelayParsing, GateDelayTwoSlots) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b, c;\n"
              "  and #(1:2:3, 4:5:6) g1(c, a, b);\n"
              "endmodule\n"));
}

// §28.16.1 R3: a procedural delay control accepts mintypmax — `#(a:b:c)`
// on a statement must land as an ExprKind::kMinTypMax on the delay slot.
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

// §28.16.1 R1: a net declaration's delay slot accepts mintypmax — the
// kMinTypMax node must surface on net_delay so the simulator can later
// pick min/typ/max per DelayMode.
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

// §28.16.1 R1: a net declaration's three delay slots each accept an
// independent mintypmax triple — rise/fall/turn-off must all carry a
// kMinTypMax node, none silently flattened.
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

// §28.16.1 R1: a cont-assign's two delay slots each accept an independent
// mintypmax triple — both rise and fall must carry a kMinTypMax node.
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

// §28.16.1 R2: min/typ/max have no required ordering — a spec where the
// literal min value exceeds typ and max must still parse cleanly, i.e.,
// there is no parse-time validator rejecting non-ascending triples.
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

// §28.16.1 R1: mintypmax slots accept identifiers, not just constants —
// e.g., parameters in each position must parse, since R1 requires
// "expressions", not numeric literals.
TEST(MinTypMaxDelayParsing, IdentifierExpressionsInTriple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter min_hi = 95, typ_hi = 100, max_hi = 105;\n"
              "  wire y, a;\n"
              "  assign #(min_hi : typ_hi : max_hi) y = a;\n"
              "endmodule\n"));
}

}  // namespace
