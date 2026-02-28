// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA302, PulldownStrength_SingleWeak0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (weak0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);  // weak0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SinglePull0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 3u);  // pull0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SingleHighz0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (highz0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 1u);  // highz0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength0 , strength1 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_Strength0Strength1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong0, pull1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 3u);  // pull1
  EXPECT_EQ(g->gate_inst_name, "pu1");
}

TEST(ParserA302, PullupStrength_Weak0Supply1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak0, supply1) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);  // weak0
  EXPECT_EQ(g->drive_strength1, 5u);  // supply1
}

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength1 , strength0 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_Strength1Strength0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (supply1, weak0) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);  // weak0
  EXPECT_EQ(g->drive_strength1, 5u);  // supply1
}

TEST(ParserA302, PullupStrength_Highz1Strong0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (highz1, strong0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 1u);  // highz1
}

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength1 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_SingleStrength1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 4u);  // strong1
}

TEST(ParserA302, PullupStrength_SingleSupply1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (supply1) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 5u);  // supply1
}

TEST(ParserA302, PullupStrength_SingleWeak1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 2u);  // weak1
}

TEST(ParserA302, PullupStrength_SinglePull1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (pull1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 3u);  // pull1
}

TEST(ParserA302, PullupStrength_SingleHighz1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (highz1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);  // none
  EXPECT_EQ(g->drive_strength1, 1u);  // highz1
}

// -----------------------------------------------------------------------------
// Combination: strength with multiple instances
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0, weak1) pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 4u);  // strong0
  EXPECT_EQ(gates[0]->drive_strength1, 2u);  // weak1
  EXPECT_EQ(gates[1]->drive_strength0, 4u);  // strong0
  EXPECT_EQ(gates[1]->drive_strength1, 2u);  // weak1
}

TEST(ParserA302, PullupStrength_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak0, strong1) pu1(a), pu2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 2u);  // weak0
  EXPECT_EQ(gates[0]->drive_strength1, 4u);  // strong1
  EXPECT_EQ(gates[1]->drive_strength0, 2u);  // weak0
  EXPECT_EQ(gates[1]->drive_strength1, 4u);  // strong1
}

TEST(ParserA302, PulldownStrength_SingleStrength0_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0) pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 3u);  // pull0
  EXPECT_EQ(gates[0]->drive_strength1, 0u);  // none
  EXPECT_EQ(gates[1]->drive_strength0, 3u);  // pull0
  EXPECT_EQ(gates[1]->drive_strength1, 0u);  // none
}

TEST(ParserA302, PullupStrength_SingleStrength1_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pullup (pull1) pu1(a), pu2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 0u);  // none
  EXPECT_EQ(gates[0]->drive_strength1, 3u);  // pull1
  EXPECT_EQ(gates[1]->drive_strength0, 0u);  // none
  EXPECT_EQ(gates[1]->drive_strength1, 3u);  // pull1
}

// -----------------------------------------------------------------------------
// All strength0 values exercised in pulldown_strength
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_AllStrength0Values) {
  // highz0=1, weak0=2, pull0=3, strong0=4, supply0=5
  EXPECT_TRUE(ParseOk("module m; pulldown (highz0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (weak0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (pull0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (strong0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (supply0) (out); endmodule"));
}

// -----------------------------------------------------------------------------
// All strength1 values exercised in pullup_strength
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_AllStrength1Values) {
  // highz1=1, weak1=2, pull1=3, strong1=4, supply1=5
  EXPECT_TRUE(ParseOk("module m; pullup (highz1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (weak1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (pull1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (strong1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (supply1) (out); endmodule"));
}

// =============================================================================
// A.3.3 Production #1: enable_terminal ::= expression
// Exercised via enable gates (bufif0/bufif1/notif0/notif1) and
// pass enable switches (tranif0/tranif1/rtranif0/rtranif1).
// The enable_terminal is the third terminal in these gate instances.
// =============================================================================
TEST(ParserA303, EnableTerminal_SimpleIdent) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA303, EnableTerminal_ComplexExpr) {
  // enable_terminal accepts any expression
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif1 (out, in, a & b);\n"
              "endmodule\n"));
}

TEST(ParserA303, EnableTerminal_BitwiseExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif0 (out, in, a | b | c);\n"
              "endmodule\n"));
}

TEST(ParserA303, EnableTerminal_TernaryExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif1 (out, in, sel ? en1 : en2);\n"
              "endmodule\n"));
}

TEST(ParserA303, EnableTerminal_BitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif0 (out, in, ctrl[2]);\n"
              "endmodule\n"));
}

TEST(ParserA303, EnableTerminal_PassEnableSwitch) {
  // enable_terminal in pass enable switch context
  auto r = Parse(
      "module m;\n"
      "  tranif1 (a, b, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA303, EnableTerminal_PassEnableExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif0 (a, b, x ^ y);\n"
              "endmodule\n"));
}

// =============================================================================
// A.3.3 Production #2: inout_terminal ::= net_lvalue
// Exercised via pass switches (tran/rtran) and
// pass enable switches (tranif0/tranif1/rtranif0/rtranif1).
// =============================================================================
TEST(ParserA303, InoutTerminal_SimpleIdent) {
  auto r = Parse(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA303, InoutTerminal_BitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tran (a[0], b[1]);\n"
              "endmodule\n"));
}

TEST(ParserA303, InoutTerminal_PartSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtran (bus[3:0], net[7:4]);\n"
              "endmodule\n"));
}

TEST(ParserA303, InoutTerminal_Concatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tran ({a, b}, {c, d});\n"
              "endmodule\n"));
}

TEST(ParserA303, InoutTerminal_PassEnableSwitch) {
  // inout_terminal positions in pass enable switches
  auto r = Parse(
      "module m;\n"
      "  tranif0 (x, y, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA303, InoutTerminal_RtranBasic) {
  auto r = Parse(
      "module m;\n"
      "  rtran (p, q);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

// =============================================================================
// A.3.3 Production #3: input_terminal ::= expression
// Exercised via n-input gates (and/nand/or/nor/xor/xnor),
// n-output gates (buf/not), cmos/mos switches.
// =============================================================================
TEST(ParserA303, InputTerminal_SimpleIdent) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA303, InputTerminal_ComplexExpr) {
  // input_terminal accepts any expression
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  or (out, a & b, c | d);\n"
              "endmodule\n"));
}

TEST(ParserA303, InputTerminal_TernaryExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  xor (out, sel ? a : b, c);\n"
              "endmodule\n"));
}

TEST(ParserA303, InputTerminal_BitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nand (out, data[0], data[1], data[2]);\n"
              "endmodule\n"));
}

TEST(ParserA303, InputTerminal_NOutputGate) {
  // input_terminal in n-output gate (last terminal is input)
  auto r = Parse(
      "module m;\n"
      "  buf (o1, o2, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA303, InputTerminal_NOutputExpr) {
  // Expression as input_terminal in not gate
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  not (out, a ^ b);\n"
              "endmodule\n"));
}

TEST(ParserA303, InputTerminal_MultipleInputs) {
  // Multiple input_terminals in n-input gate
  auto r = Parse(
      "module m;\n"
      "  nor (out, a, b, c, d, e);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 6u);
}

TEST(ParserA303, InputTerminal_CmosSwitch) {
  // input_terminal as second terminal of cmos switch
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cmos (out, data[3:0], nctrl, pctrl);\n"
              "endmodule\n"));
}

// =============================================================================
// A.3.3 Production #4: ncontrol_terminal ::= expression
// Exercised via cmos switches (cmos/rcmos).
// The ncontrol_terminal is the third terminal.
// =============================================================================
TEST(ParserA303, NcontrolTerminal_SimpleIdent) {
  auto r = Parse(
      "module m;\n"
      "  cmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA303, NcontrolTerminal_ComplexExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cmos (out, in, a & b, pctrl);\n"
              "endmodule\n"));
}

TEST(ParserA303, NcontrolTerminal_BitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rcmos (out, in, ctrl[0], ctrl[1]);\n"
              "endmodule\n"));
}

TEST(ParserA303, NcontrolTerminal_TernaryExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cmos (out, in, sel ? n1 : n2, pctrl);\n"
              "endmodule\n"));
}

// =============================================================================
// A.3.3 Production #5: output_terminal ::= net_lvalue
// Exercised via all gate types that have output terminals:
// n-input gates, n-output gates, enable gates, mos/cmos switches, pull gates.
// =============================================================================
TEST(ParserA303, OutputTerminal_SimpleIdent) {
  auto r = Parse(
      "module m;\n"
      "  and (y, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA303, OutputTerminal_BitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and (out[0], a, b);\n"
              "endmodule\n"));
}

TEST(ParserA303, OutputTerminal_PartSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  buf (out[3:0], in);\n"
              "endmodule\n"));
}

TEST(ParserA303, OutputTerminal_Concatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  buf ({o1, o2}, in);\n"
              "endmodule\n"));
}

TEST(ParserA303, OutputTerminal_MultipleOutputs) {
  // Multiple output_terminals in n-output gate
  auto r = Parse(
      "module m;\n"
      "  buf (o1, o2, o3, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA303, OutputTerminal_PullGate) {
  // output_terminal in pull gate (single terminal)
  auto r = Parse(
      "module m;\n"
      "  pullup (net_a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(ParserA303, OutputTerminal_PullGateBitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  pulldown (bus[2]);\n"
              "endmodule\n"));
}

TEST(ParserA303, OutputTerminal_EnableGate) {
  // output_terminal as first terminal of enable gate
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif0 (out[7:0], in, en);\n"
              "endmodule\n"));
}

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
