// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.3.3 Production #6: pcontrol_terminal ::= expression
// Exercised via cmos switches (cmos/rcmos).
// The pcontrol_terminal is the fourth terminal.
// =============================================================================
TEST(ParserA303, PcontrolTerminal_SimpleIdent) {
  auto r = Parse(
      "module m;\n"
      "  rcmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA303, PcontrolTerminal_ComplexExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rcmos (out, in, nctrl, x | y);\n"
              "endmodule\n"));
}

TEST(ParserA303, PcontrolTerminal_BitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cmos (out, in, nctrl, ctrl[1]);\n"
              "endmodule\n"));
}

TEST(ParserA303, PcontrolTerminal_TernaryExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rcmos (out, in, nctrl, sel ? p1 : p2);\n"
              "endmodule\n"));
}

// =============================================================================
// Combined: all 6 terminal types in a single module
// =============================================================================
TEST(ParserA303, AllTerminalTypes) {
  auto r = Parse(
      "module m;\n"
      "  // output_terminal + input_terminal (n-input gate)\n"
      "  and (y, a, b);\n"
      "  // output_terminal + input_terminal (n-output gate)\n"
      "  buf (o1, o2, in);\n"
      "  // output_terminal + input_terminal + enable_terminal\n"
      "  bufif0 (out, data, en);\n"
      "  // output_terminal + input_terminal + ncontrol_terminal + "
      "pcontrol_terminal\n"
      "  cmos (out2, data2, nc, pc);\n"
      "  // inout_terminal + inout_terminal\n"
      "  tran (p, q);\n"
      "  // inout_terminal + inout_terminal + enable_terminal\n"
      "  tranif1 (r, s, ctrl);\n"
      "  // output_terminal (pull gate)\n"
      "  pullup (vdd);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 7u);
}

// =============================================================================
// A.3.4 Production #1: cmos_switchtype ::= cmos | rcmos
// =============================================================================
TEST(ParserA304, CmosSwitchtype_Cmos) {
  auto r = Parse(
      "module m;\n"
      "  cmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA304, CmosSwitchtype_Rcmos) {
  auto r = Parse(
      "module m;\n"
      "  rcmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

// =============================================================================
// A.3.4 Production #2: enable_gatetype ::= bufif0 | bufif1 | notif0 | notif1
// =============================================================================
TEST(ParserA304, EnableGatetype_Bufif0) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, EnableGatetype_Bufif1) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, EnableGatetype_Notif0) {
  auto r = Parse(
      "module m;\n"
      "  notif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, EnableGatetype_Notif1) {
  auto r = Parse(
      "module m;\n"
      "  notif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.4 Production #3: mos_switchtype ::= nmos | pmos | rnmos | rpmos
// =============================================================================
TEST(ParserA304, MosSwitchtype_Nmos) {
  auto r = Parse(
      "module m;\n"
      "  nmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, MosSwitchtype_Pmos) {
  auto r = Parse(
      "module m;\n"
      "  pmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, MosSwitchtype_Rnmos) {
  auto r = Parse(
      "module m;\n"
      "  rnmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRnmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, MosSwitchtype_Rpmos) {
  auto r = Parse(
      "module m;\n"
      "  rpmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRpmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.4 Production #4: n_input_gatetype ::= and | nand | or | nor | xor | xnor
// =============================================================================
TEST(ParserA304, NInputGatetype_And) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Nand) {
  auto r = Parse(
      "module m;\n"
      "  nand (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Or) {
  auto r = Parse(
      "module m;\n"
      "  or (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Nor) {
  auto r = Parse(
      "module m;\n"
      "  nor (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Xor) {
  auto r = Parse(
      "module m;\n"
      "  xor (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Xnor) {
  auto r = Parse(
      "module m;\n"
      "  xnor (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXnor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.4 Production #5: n_output_gatetype ::= buf | not
// =============================================================================
TEST(ParserA304, NOutputGatetype_Buf) {
  auto r = Parse(
      "module m;\n"
      "  buf (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA304, NOutputGatetype_Not) {
  auto r = Parse(
      "module m;\n"
      "  not (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

// =============================================================================
// A.3.4 Production #6: pass_en_switchtype ::= tranif0 | tranif1 | rtranif1 |
// rtranif0
// =============================================================================
TEST(ParserA304, PassEnSwitchtype_Tranif0) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, PassEnSwitchtype_Tranif1) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, PassEnSwitchtype_Rtranif0) {
  auto r = Parse(
      "module m;\n"
      "  rtranif0 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, PassEnSwitchtype_Rtranif1) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.4 Production #7: pass_switchtype ::= tran | rtran
// =============================================================================
TEST(ParserA304, PassSwitchtype_Tran) {
  auto r = Parse(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA304, PassSwitchtype_Rtran) {
  auto r = Parse(
      "module m;\n"
      "  rtran (a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

}  // namespace
