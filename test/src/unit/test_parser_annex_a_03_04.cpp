#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SwitchInstanceParsing, CmosSwitchType_Cmos) {
  auto r = Parse(
      "module m;\n"
      "  cmos g1(out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(SwitchInstanceParsing, CmosSwitchType_Rcmos) {
  auto r = Parse(
      "module m;\n"
      "  rcmos g1(out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(SwitchInstanceParsing, EnableGateType_Bufif0) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, EnableGateType_Bufif1) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, EnableGateType_Notif0) {
  auto r = Parse(
      "module m;\n"
      "  notif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, EnableGateType_Notif1) {
  auto r = Parse(
      "module m;\n"
      "  notif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, MosSwitchType_Nmos) {
  auto r = Parse(
      "module m;\n"
      "  nmos (out, in, gate);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, MosSwitchType_Pmos) {
  auto r = Parse(
      "module m;\n"
      "  pmos (out, in, gate);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, MosSwitchType_Rnmos) {
  auto r = Parse(
      "module m;\n"
      "  rnmos (out, in, gate);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRnmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, MosSwitchType_Rpmos) {
  auto r = Parse(
      "module m;\n"
      "  rpmos (out, in, gate);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRpmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, NInputGateType_And) {
  auto r = Parse(
      "module m;\n"
      "  and (y, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, NInputGateType_Nand) {
  auto r = Parse(
      "module m;\n"
      "  nand (y, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
}

TEST(SwitchInstanceParsing, NInputGateType_Or) {
  auto r = Parse(
      "module m;\n"
      "  or (y, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
}

TEST(SwitchInstanceParsing, NInputGateType_Nor) {
  auto r = Parse(
      "module m;\n"
      "  nor (y, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNor);
  ASSERT_NE(g, nullptr);
}

TEST(SwitchInstanceParsing, NInputGateType_Xor) {
  auto r = Parse(
      "module m;\n"
      "  xor (y, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXor);
  ASSERT_NE(g, nullptr);
}

TEST(SwitchInstanceParsing, NInputGateType_Xnor) {
  auto r = Parse(
      "module m;\n"
      "  xnor (y, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXnor);
  ASSERT_NE(g, nullptr);
}

TEST(SwitchInstanceParsing, NOutputGateType_Buf) {
  auto r = Parse(
      "module m;\n"
      "  buf (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(SwitchInstanceParsing, NOutputGateType_Not) {
  auto r = Parse(
      "module m;\n"
      "  not (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(SwitchInstanceParsing, PassEnSwitchType_Tranif0) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(SwitchInstanceParsing, PassEnSwitchType_Tranif1) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
}

TEST(SwitchInstanceParsing, PassEnSwitchType_Rtranif0) {
  auto r = Parse(
      "module m;\n"
      "  rtranif0 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
}

TEST(SwitchInstanceParsing, PassEnSwitchType_Rtranif1) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1);
  ASSERT_NE(g, nullptr);
}

TEST(SwitchInstanceParsing, PassSwitchType_Tran) {
  auto r = Parse(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(SwitchInstanceParsing, PassSwitchType_Rtran) {
  auto r = Parse(
      "module m;\n"
      "  rtran (a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(SwitchInstanceParsing, PullGate_Pullup) {
  auto r = Parse(
      "module m;\n"
      "  pullup (net_a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(SwitchInstanceParsing, PullGate_Pulldown) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (net_a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(SwitchInstanceParsing, AllGateTypesWithNamedInstances) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b);\n"
      "  nand g2(y, a, b);\n"
      "  or g3(y, a, b);\n"
      "  nor g4(y, a, b);\n"
      "  xor g5(y, a, b);\n"
      "  xnor g6(y, a, b);\n"
      "  buf g7(out, in);\n"
      "  not g8(out, in);\n"
      "  bufif0 g9(out, in, en);\n"
      "  bufif1 g10(out, in, en);\n"
      "  notif0 g11(out, in, en);\n"
      "  notif1 g12(out, in, en);\n"
      "  nmos g13(out, in, gate);\n"
      "  pmos g14(out, in, gate);\n"
      "  rnmos g15(out, in, gate);\n"
      "  rpmos g16(out, in, gate);\n"
      "  cmos g17(out, in, nc, pc);\n"
      "  rcmos g18(out, in, nc, pc);\n"
      "  tran g19(a, b);\n"
      "  rtran g20(a, b);\n"
      "  tranif0 g21(a, b, en);\n"
      "  tranif1 g22(a, b, en);\n"
      "  rtranif0 g23(a, b, en);\n"
      "  rtranif1 g24(a, b, en);\n"
      "  pullup g25(vdd);\n"
      "  pulldown g26(gnd);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 26u);

  EXPECT_EQ(gates[0]->gate_inst_name, "g1");
  EXPECT_EQ(gates[0]->gate_kind, GateKind::kAnd);
  EXPECT_EQ(gates[25]->gate_inst_name, "g26");
  EXPECT_EQ(gates[25]->gate_kind, GateKind::kPulldown);
}

TEST(PrimitiveGateTypeParsing, AllGateAndSwitchTypes) {
  auto r = Parse(
      "module m;\n"
      "  // cmos_switchtype\n"
      "  cmos (o1, i1, nc1, pc1);\n"
      "  rcmos (o2, i2, nc2, pc2);\n"
      "  // enable_gatetype\n"
      "  bufif0 (o3, i3, e3);\n"
      "  bufif1 (o4, i4, e4);\n"
      "  notif0 (o5, i5, e5);\n"
      "  notif1 (o6, i6, e6);\n"
      "  // mos_switchtype\n"
      "  nmos (o7, i7, c7);\n"
      "  pmos (o8, i8, c8);\n"
      "  rnmos (o9, i9, c9);\n"
      "  rpmos (o10, i10, c10);\n"
      "  // n_input_gatetype\n"
      "  and (o11, a11, b11);\n"
      "  nand (o12, a12, b12);\n"
      "  or (o13, a13, b13);\n"
      "  nor (o14, a14, b14);\n"
      "  xor (o15, a15, b15);\n"
      "  xnor (o16, a16, b16);\n"
      "  // n_output_gatetype\n"
      "  buf (o17, i17);\n"
      "  not (o18, i18);\n"
      "  // pass_en_switchtype\n"
      "  tranif0 (a19, b19, c19);\n"
      "  tranif1 (a20, b20, c20);\n"
      "  rtranif0 (a21, b21, c21);\n"
      "  rtranif1 (a22, b22, c22);\n"
      "  // pass_switchtype\n"
      "  tran (a23, b23);\n"
      "  rtran (a24, b24);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);

  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRnmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRpmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNand), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kOr), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNor), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kXor), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kXnor), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNot), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTran), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran), nullptr);
}

TEST(PrimitiveGateTypeParsing, NInputGatetype_And) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, NInputGatetype_Nand) {
  auto r = Parse(
      "module m;\n"
      "  nand (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, NInputGatetype_Or) {
  auto r = Parse(
      "module m;\n"
      "  or (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, NInputGatetype_Nor) {
  auto r = Parse(
      "module m;\n"
      "  nor (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, NInputGatetype_Xor) {
  auto r = Parse(
      "module m;\n"
      "  xor (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, NInputGatetype_Xnor) {
  auto r = Parse(
      "module m;\n"
      "  xnor (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXnor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, NOutputGatetype_Buf) {
  auto r = Parse(
      "module m;\n"
      "  buf (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PrimitiveGateTypeParsing, NOutputGatetype_Not) {
  auto r = Parse(
      "module m;\n"
      "  not (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Bufif0) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Bufif1) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Notif0) {
  auto r = Parse(
      "module m;\n"
      "  notif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, EnableGatetype_Notif1) {
  auto r = Parse(
      "module m;\n"
      "  notif1 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, MosSwitchtype_Nmos) {
  auto r = Parse(
      "module m;\n"
      "  nmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, MosSwitchtype_Pmos) {
  auto r = Parse(
      "module m;\n"
      "  pmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, MosSwitchtype_Rnmos) {
  auto r = Parse(
      "module m;\n"
      "  rnmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRnmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, MosSwitchtype_Rpmos) {
  auto r = Parse(
      "module m;\n"
      "  rpmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRpmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, PassEnSwitchtype_Tranif0) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, PassEnSwitchtype_Tranif1) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, PassEnSwitchtype_Rtranif0) {
  auto r = Parse(
      "module m;\n"
      "  rtranif0 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, PassEnSwitchtype_Rtranif1) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 (a, b, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveGateTypeParsing, PassSwitchtype_Tran) {
  auto r = Parse(
      "module m;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PrimitiveGateTypeParsing, PassSwitchtype_Rtran) {
  auto r = Parse(
      "module m;\n"
      "  rtran (a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PrimitiveGateTypeParsing, CmosSwitchtype_Cmos) {
  auto r = Parse(
      "module m;\n"
      "  cmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(PrimitiveGateTypeParsing, CmosSwitchtype_Rcmos) {
  auto r = Parse(
      "module m;\n"
      "  rcmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

}  // namespace
