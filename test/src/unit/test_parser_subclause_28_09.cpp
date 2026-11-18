#include <gtest/gtest.h>

#include <cstddef>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(CmosSwitches, CmosRejectsFiveTerminals) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data, nctrl, pctrl, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "incorrect number of terminals for gate instance", 2, "28.3"));
}

TEST(CmosSwitches, CmosRejectsThreeTerminals) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data, nctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "incorrect number of terminals for gate instance", 2, "28.3"));
}

TEST(CmosSwitches, CmosRejectsTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, data);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "incorrect number of terminals for gate instance", 2, "28.3"));
}

TEST(CmosSwitches, RcmosRejectsFiveTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rcmos r1(out, data, nctrl, pctrl, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "incorrect number of terminals for gate instance", 2, "28.3"));
}

TEST(CmosSwitches, RcmosRejectsThreeTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rcmos r1(out, data, nctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "incorrect number of terminals for gate instance", 2, "28.3"));
}

TEST(CmosSwitches, RcmosRejectsTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  rcmos r1(out, data);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "incorrect number of terminals for gate instance", 2, "28.3"));
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

TEST(CmosSwitches, CmosTooManyDelaysRejected) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(1, 2, 3, 4) c1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ','", 2, "28.16"));
}

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

TEST(CmosSwitches, RcmosTwoValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  rcmos #(4, 6) r1(o, i, n, p);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 4u);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_fall->int_val, 6u);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

TEST(CmosSwitches, RcmosOneValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  rcmos #5 r1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 5u);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

TEST(CmosSwitches, RcmosNoDelaySpec) {
  auto r = Parse(
      "module m;\n"
      "  rcmos r1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

TEST(CmosSwitches, RcmosTooManyDelaysRejected) {
  auto r = Parse(
      "module m;\n"
      "  rcmos #(1, 2, 3, 4) r1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ','", 2, "28.16"));
}

TEST(CmosSwitches, RcmosTerminalOrderIsOutDataNctrlPctrl) {
  auto r = Parse(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  rcmos r1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  ASSERT_EQ(g->gate_terminals.size(), 4u);
  EXPECT_EQ(g->gate_terminals[0]->text, "out");
  EXPECT_EQ(g->gate_terminals[1]->text, "data");
  EXPECT_EQ(g->gate_terminals[2]->text, "nctrl");
  EXPECT_EQ(g->gate_terminals[3]->text, "pctrl");
}

TEST(CmosSwitches, SeveralRcmosInstancesInOneDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  rcmos r1(o1, d1, n1, p1), r2(o2, d2, n2, p2), r3(o3, d3, n3, p3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 3u);
  const char* const kNames[] = {"r1", "r2", "r3"};
  const char* const kOuts[] = {"o1", "o2", "o3"};
  const char* const kPctrls[] = {"p1", "p2", "p3"};
  for (std::size_t i = 0; i < gates.size(); ++i) {
    EXPECT_EQ(gates[i]->gate_kind, GateKind::kRcmos) << i;
    EXPECT_EQ(gates[i]->gate_inst_name, kNames[i]) << i;
    ASSERT_EQ(gates[i]->gate_terminals.size(), 4u) << i;
    EXPECT_EQ(gates[i]->gate_terminals[0]->text, kOuts[i]) << i;
    EXPECT_EQ(gates[i]->gate_terminals[3]->text, kPctrls[i]) << i;
  }
}

}  // namespace
