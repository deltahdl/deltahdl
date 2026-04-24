// §28.9

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(CmosSwitches, CmosRejectsFiveTerminals) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data, nctrl, pctrl, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CmosSwitches, CmosRejectsThreeTerminals) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data, nctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CmosSwitches, CmosRejectsTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CmosSwitches, RcmosRejectsFiveTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rcmos r1(out, data, nctrl, pctrl, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CmosSwitches, RcmosRejectsThreeTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rcmos r1(out, data, nctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CmosSwitches, RcmosRejectsTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rcmos r1(out, data);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CmosSwitches, NamedCmosInstantiation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  cmos c1(out, data, ncontrol, pcontrol);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kCmos);
  EXPECT_EQ(item->gate_inst_name, "c1");
  ASSERT_EQ(item->gate_terminals.size(), 4);
}

TEST(CmosSwitches, NamedRcmosInstantiation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  rcmos r1(out, data, ncontrol, pcontrol);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kRcmos);
  EXPECT_EQ(item->gate_inst_name, "r1");
  ASSERT_EQ(item->gate_terminals.size(), 4);
}

// cmos and rcmos must parse to distinct GateKind values so elaboration can
// apply the resistive strength reduction to rcmos only.
TEST(CmosSwitches, CmosAndRcmosParseToDistinctGateKinds) {
  auto r = Parse(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos  c1(out, data, nctrl, pctrl);\n"
      "  rcmos r1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos), nullptr);
}

// Two-delay form: both values must land in their slots, leaving the decay
// slot null so the simulator reuses the fall value for turn-off.
TEST(CmosSwitches, CmosTwoValueDelay) {
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

// Three-delay form: cmos is delay3-capable, so a full `#(r, f, z)` triple
// must parse cleanly (the rise/fall/decay-to-x selection happens later).
TEST(CmosSwitches, CmosThreeValueDelay) {
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

// rcmos accepts the same delay3 form as cmos; all three fields must surface.
TEST(CmosSwitches, RcmosThreeValueDelay) {
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

// Distinct int values pin the slot assignment: position 1 → rise,
// position 2 → fall, position 3 → transition-to-z. A regression that
// swapped any pair would leave the values crossed.
TEST(CmosSwitches, CmosThreeValueDelayMapsToRiseFallDecay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(11, 22, 33) c1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 11u);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_fall->int_val, 22u);
  ASSERT_NE(g->gate_delay_decay, nullptr);
  EXPECT_EQ(g->gate_delay_decay->int_val, 33u);
}

// A single delay applies to every output transition; only the rise slot
// should be populated by the parser.
TEST(CmosSwitches, CmosOneValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #4 c1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 4u);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

// With no delay spec, all three slots stay null and the switch has no
// propagation delay.
TEST(CmosSwitches, CmosNoDelaySpec) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

// A fourth delay term exceeds the cap; guards against a silent drop of the
// extra value.
TEST(CmosSwitches, CmosTooManyDelaysRejected) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(1, 2, 3, 4) c1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The terminal list ordering is (out, data, ncontrol, pcontrol). Pinning
// identifier text at each position catches any reordering regression.
TEST(CmosSwitches, CmosTerminalOrderIsOutDataNctrlPctrl) {
  auto r = Parse(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  ASSERT_EQ(g->gate_terminals.size(), 4u);
  EXPECT_EQ(g->gate_terminals[0]->text, "out");
  EXPECT_EQ(g->gate_terminals[1]->text, "data");
  EXPECT_EQ(g->gate_terminals[2]->text, "nctrl");
  EXPECT_EQ(g->gate_terminals[3]->text, "pctrl");
}

}  // namespace
