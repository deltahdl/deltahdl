#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(GateDelayParsing, PullupDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  pullup #5 pu1(net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GateDelayParsing, PulldownDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  pulldown #5 pd1(net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GateDelayParsing, NInputGateThreeValueDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  and #(1, 2, 3) a1(o, i1, i2);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DelayParsing, AndGateSingleValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #5 g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 5u);
  EXPECT_EQ(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_decay, nullptr);
}

TEST(DelayParsing, AndGateTwoValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #(10, 20) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 10u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 20u);
  EXPECT_EQ(item->gate_delay_decay, nullptr);
}

TEST(DelayParsing, ThreeStateGateThreeValueDelayAccepted) {
  // §28.3.3: a delay specification can carry up to three delay values
  // depending on the gate type. A three-state gate is a delay3 gate, so its
  // declaration accepts the rise/fall/turn-off triple without diagnostics.
  auto r = Parse(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif0 #(1, 2, 3) g1(y, a, en);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 1u);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_fall->int_val, 2u);
  ASSERT_NE(g->gate_delay_decay, nullptr);
  EXPECT_EQ(g->gate_delay_decay->int_val, 3u);
}

TEST(DelayParsing, NOutputGateTwoValueDelayAccepted) {
  // §28.3.3: the number of delay values allowed depends on the gate type. An
  // n_output gate (buf/not) is a delay2 primitive, so its declaration accepts a
  // rise/fall pair and exposes no third (turn-off) slot.
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  buf #(2, 3) g1(y, a);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 2u);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_fall->int_val, 3u);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

TEST(DelayParsing, MosSwitchThreeValueDelayAccepted) {
  // §28.3.3: a MOS switch is a delay3 primitive, so — like a three-state gate —
  // its declaration accepts the full rise/fall/turn-off delay triple. This
  // exercises the delay on a switch declaration rather than a logic gate.
  auto r = Parse(
      "module m;\n"
      "  wire y, a, ctl;\n"
      "  nmos #(1, 2, 3) s1(y, a, ctl);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(s, nullptr);
  ASSERT_NE(s->gate_delay, nullptr);
  EXPECT_EQ(s->gate_delay->int_val, 1u);
  ASSERT_NE(s->gate_delay_fall, nullptr);
  EXPECT_EQ(s->gate_delay_fall->int_val, 2u);
  ASSERT_NE(s->gate_delay_decay, nullptr);
  EXPECT_EQ(s->gate_delay_decay->int_val, 3u);
}

TEST(GateDelayParsing, GateWithoutDelayHasNullDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

}  // namespace
