#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(GateDelayParsing, NInputGateRiseFallDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  or #(3, 5) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 3u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 5u);
}

TEST(GateDelayParsing, PassSwitchDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  tran #5 t1(a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

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

TEST(GateDelayParsing, NOutputGateThreeValueDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  buf #(1, 2, 3) b1(o, i);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GateDelayParsing, NOutputGateSingleValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  buf #5 b1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 5u);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
}

TEST(GateDelayParsing, PassEnableSwitchSingleValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 #7 t1(a, b, c);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 7u);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
}

TEST(GateDelayParsing, PassEnableSwitchThreeValueDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 #(2, 4, 6) t1(a, b, c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GateDelayParsing, MosSwitchTwoValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  nmos #(3, 5) n1(o, i, g);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 3u);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_fall->int_val, 5u);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

TEST(GateDelayParsing, MosSwitchThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  pmos #(2, 3, 4) p1(o, i, g);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
  EXPECT_NE(g->gate_delay_decay, nullptr);
}

TEST(GateDelayParsing, CmosSwitchTwoValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(3, 5) c1(o, i, n, p);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 3u);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_fall->int_val, 5u);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
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

TEST(DelayParsing, XorGateSingleValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xor #7 g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 7u);
}

TEST(DelayParsing, Bufif0GateThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  bufif0 #(5, 10, 15) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 5u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 10u);
  ASSERT_NE(item->gate_delay_decay, nullptr);
  EXPECT_EQ(item->gate_delay_decay->int_val, 15u);
}

TEST(EnableGates, ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 #(10, 20, 30) b1(out, in, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

TEST(MosSwitches, ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  nmos #(10, 20, 30) n1(out, data, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
}

TEST(PassSwitches, DelayNotAllowed) {
  auto r = Parse(
      "module m;\n"
      "  tran #5 (a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassSwitches, RtranDelayNotAllowed) {
  auto r = Parse(
      "module m;\n"
      "  rtran #5 (a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, TwoValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 #(10, 20) t1(a, b, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
}

TEST(CmosSwitches, ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(10, 20, 30) c1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
}

// When no `#` appears, all three delay fields remain null — the zero-delay
// baseline §28.3.3 permits.
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

TEST(GateDelayParsing, RnmosThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  rnmos #(1, 2, 3) r1(o, i, g);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRnmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

TEST(GateDelayParsing, RpmosThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  rpmos #(4, 5, 6) r1(o, i, g);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRpmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

TEST(GateDelayParsing, RcmosThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  rcmos #(7, 8, 9) r1(o, i, n, p);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

TEST(GateDelayParsing, Notif0ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  notif0 #(1, 2, 3) n1(o, i, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

TEST(GateDelayParsing, Notif1ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  notif1 #(4, 5, 6) n1(o, i, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

TEST(GateDelayParsing, Rtranif0TwoValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  rtranif0 #(3, 4) r1(a, b, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

TEST(GateDelayParsing, Rtranif1ThreeValueDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 #(1, 2, 3) r1(a, b, en);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
