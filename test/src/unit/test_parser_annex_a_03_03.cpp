// Annex A.3.3: Primitive terminals

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

}  // namespace
