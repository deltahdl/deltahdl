// §28.8

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(PassSwitches, TranRejectsSingleTerminal) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(a);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, Tranif0RejectsTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 t1(a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, Tranif1RejectsFourTerminals) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 t1(a, b, en, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 t1(a1, b1, en), t2(a2, b2, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(PassSwitches, UnnamedTranInstantiation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kTran);
  ASSERT_EQ(item->gate_terminals.size(), 2);
}

TEST(PassEnableSwitches, Tranif1Instantiation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PassSwitches, TranRejectsDelay) {
  auto r = Parse(
      "module m;\n"
      "  tran #5 t1(a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassSwitches, RtranRejectsDelay) {
  auto r = Parse(
      "module m;\n"
      "  rtran #5 (a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, Tranif0AcceptsSingleValueDelay) {
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

TEST(PassEnableSwitches, Tranif1RejectsThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 #(2, 4, 6) t1(a, b, c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, Tranif0AcceptsTwoValueDelay) {
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

TEST(PassEnableSwitches, Rtranif0AcceptsTwoValueDelay) {
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

TEST(PassEnableSwitches, Rtranif1RejectsThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 #(1, 2, 3) r1(a, b, en);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// tran takes exactly two signal terminals; a third must be rejected.
TEST(PassSwitches, TranRejectsThreeTerminals) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(a, b, c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// rtran shares tran's two-terminal rule.
TEST(PassSwitches, RtranAcceptsTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rtran r1(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PassSwitches, RtranRejectsSingleTerminal) {
  auto r = Parse(
      "module m;\n"
      "  rtran r1(a);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassSwitches, RtranRejectsThreeTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rtran r1(a, b, c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, Rtranif0Instantiation) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, en;\n"
      "  rtranif0 r1(a, b, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PassEnableSwitches, Rtranif1Instantiation) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, en;\n"
      "  rtranif1 r1(a, b, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PassEnableSwitches, Rtranif0RejectsTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rtranif0 r1(a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PassEnableSwitches, Rtranif1RejectsFourTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 r1(a, b, en, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// Positive counterpart to RtranAcceptsTwoTerminals.
TEST(PassSwitches, TranAcceptsTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

// Mirrors Tranif0AcceptsSingleValueDelay so both enable variants are
// exercised for the single-delay form.
TEST(PassEnableSwitches, Tranif1AcceptsSingleValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 #4 t1(a, b, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 4u);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
}

// When the source omits the delay spec entirely all delay slots stay null,
// matching the no-turn-on / no-turn-off rule for bidirectional pass switches.
TEST(PassEnableSwitches, Tranif0WithoutDelayLeavesGateDelayNull) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

// All six bidirectional pass switch keywords parse to distinct GateKind values
// so later stages can dispatch on them.
TEST(PassSwitches, AllSixKindsParseToDistinctGateKinds) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tran     t1(a, b);\n"
      "  rtran    t2(a, b);\n"
      "  tranif0  t3(a, b, en);\n"
      "  tranif1  t4(a, b, en);\n"
      "  rtranif0 t5(a, b, en);\n"
      "  rtranif1 t6(a, b, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTran), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1),
            nullptr);
}

}  // namespace
