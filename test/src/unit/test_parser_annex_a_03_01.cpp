#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(PrimitiveInstantiationParsing, GateInst_AndBasic) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, GateInst_NandBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nand (out, a, b);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_OrBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  or (out, a, b);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_NorBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nor (out, a, b);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_XorBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  xor (out, a, b);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_XnorBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  xnor (out, a, b);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_NInputWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  or #(3, 5) o1(out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
}

TEST(PrimitiveInstantiationParsing, GateInst_NInputMultipleInputs) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 5u);
}

TEST(PrimitiveInstantiationParsing, NInputGateInst_TwoInputs) {
  auto r = Parse(
      "module m;\n"
      "  and a1(out, in1, in2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "a1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, NInputGateInst_FourInputs) {
  auto r = Parse(
      "module m;\n"
      "  nand n1(out, a, b, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 5u);
}

TEST(PrimitiveInstantiationParsing, NInputGateInst_EightInputs) {
  auto r = Parse(
      "module m;\n"
      "  xor x1(out, a, b, c, d, e, f, g, h);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 9u);
}

TEST(PrimitiveInstantiationParsing, NInputGateInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  or (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(PrimitiveInstantiationParsing, GateInst_AllNInputGateTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and  a1(o, i1, i2);\n"
              "  nand n1(o, i1, i2);\n"
              "  or   o1(o, i1, i2);\n"
              "  nor  r1(o, i1, i2);\n"
              "  xor  x1(o, i1, i2);\n"
              "  xnor z1(o, i1, i2);\n"
              "endmodule\n"));
}

TEST(GateInstantiationParsing, GateInst_NInputGateCount) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b, c);\n"
      "  nand g2(y2, a, b);\n"
      "  xor g3(y3, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int gate_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGateInst) gate_count++;
  }
  EXPECT_EQ(gate_count, 3);
}

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

TEST(NInputGateInstantiation, NandGateBasic) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, y;\n"
      "  nand g1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_gate = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGateInst) has_gate = true;
  }
  EXPECT_TRUE(has_gate);
}

TEST(BuiltInNInputGates, AllSixGateTypes) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and  g1(y, a, b);\n"
      "  nand g2(y, a, b);\n"
      "  or   g3(y, a, b);\n"
      "  nor  g4(y, a, b);\n"
      "  xor  g5(y, a, b);\n"
      "  xnor g6(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 6u);
}

TEST(GateInstantiation, ModuleInstantiatesPrimitive) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b, y;\n"
              "  and g1(y, a, b);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_BufBasic) {
  auto r = Parse(
      "module m;\n"
      "  buf (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, GateInst_NotBasic) {
  auto r = Parse(
      "module m;\n"
      "  not (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, GateInst_NOutputMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  buf (o1, o2, o3, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(PrimitiveInstantiationParsing, NOutputGateInst_SingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, NOutputGateInst_ThreeOutputs) {
  auto r = Parse(
      "module m;\n"
      "  not n1(o1, o2, o3, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(PrimitiveInstantiationParsing, NOutputGateInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  buf (o1, o2, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(BuiltInNOutputGates, BufAndNotGates) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, y1, y2;\n"
              "  buf  g1(y1, a);\n"
              "  not  g2(y2, a);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_Bufif0Basic) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, GateInst_Bufif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_Notif0Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif0 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_Notif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  notif1 (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, EnableGateInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, EnableGateInst_Named) {
  auto r = Parse(
      "module m;\n"
      "  notif1 n1(out, in, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "n1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, GateInst_AllEnableGateTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bufif0 b0(o, i, c);\n"
              "  bufif1 b1(o, i, c);\n"
              "  notif0 n0(o, i, c);\n"
              "  notif1 n1(o, i, c);\n"
              "endmodule\n"));
}

TEST(BuiltInEnableGates, ThreeStateGates) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, en, y;\n"
              "  bufif0 g1(y, a, en);\n"
              "  bufif1 g2(y, a, en);\n"
              "  notif0 g3(y, a, en);\n"
              "  notif1 g4(y, a, en);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_NmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  nmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, GateInst_PmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  pmos (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, GateInst_RnmosBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rnmos (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_RpmosBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rpmos (out, in, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_MosWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  nmos #10 n1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_inst_name, "n1");
}

TEST(PrimitiveInstantiationParsing, MosSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  nmos (out, in, gate);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(PrimitiveInstantiationParsing, MosSwitchInst_Named) {
  auto r = Parse(
      "module m;\n"
      "  pmos p1(out, in, gate);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "p1");
}

TEST(PrimitiveInstantiationParsing, GateInst_AllMosSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nmos  n1(o, i, g);\n"
              "  pmos  p1(o, i, g);\n"
              "  rnmos rn1(o, i, g);\n"
              "  rpmos rp1(o, i, g);\n"
              "endmodule\n"));
}

TEST(MosSwitches, AllFourMosTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire out, in, gate;\n"
              "  nmos  g1(out, in, gate);\n"
              "  pmos  g2(out, in, gate);\n"
              "  rnmos g3(out, in, gate);\n"
              "  rpmos g4(out, in, gate);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_Tranif0Basic) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, GateInst_Tranif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tranif1 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_Rtranif0Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif0 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_Rtranif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif1 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_PassEnWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 #(3, 5) t1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(PrimitiveInstantiationParsing, GateInst_TranBasic) {
  auto r = Parse(
      "module m;\n"
      "  tran (io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, GateInst_RtranBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtran (io1, io2);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, PassSwitchInst_TranNamed) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, PassSwitchInst_RtranNamed) {
  auto r = Parse(
      "module m;\n"
      "  rtran rt1(io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(PrimitiveInstantiationParsing, PassSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  tran (io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(PrimitiveInstantiationParsing, PassEnSwitchInst_Tranif0Named) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 t1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(PrimitiveInstantiationParsing, PassEnSwitchInst_Tranif1Named) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 t1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
}

TEST(PrimitiveInstantiationParsing, PassEnSwitchInst_Rtranif0Named) {
  auto r = Parse(
      "module m;\n"
      "  rtranif0 rt1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(PrimitiveInstantiationParsing, PassEnSwitchInst_Rtranif1Named) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 rt1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(PrimitiveInstantiationParsing, PassEnSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(PrimitiveInstantiationParsing, GateInst_AllPassSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tran  t1(a, b);\n"
              "  rtran rt1(a, b);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_AllPassEnSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tranif0  t0(a, b, c);\n"
              "  tranif1  t1(a, b, c);\n"
              "  rtranif0 rt0(a, b, c);\n"
              "  rtranif1 rt1(a, b, c);\n"
              "endmodule\n"));
}

TEST(BidirectionalPassSwitches, TranAndRtran) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b;\n"
              "  tran  g1(a, b);\n"
              "  rtran g2(a, b);\n"
              "endmodule\n"));
}

TEST(BidirectionalPassSwitches, ConditionalPassEnables) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b, en;\n"
              "  tranif0  g1(a, b, en);\n"
              "  tranif1  g2(a, b, en);\n"
              "  rtranif0 g3(a, b, en);\n"
              "  rtranif1 g4(a, b, en);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_CmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  cmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(PrimitiveInstantiationParsing, GateInst_RcmosBasic) {
  auto r = Parse(
      "module m;\n"
      "  rcmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(PrimitiveInstantiationParsing, GateInst_CmosWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #5 (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(PrimitiveInstantiationParsing, GateInst_CmosWithThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  cmos #(2, 3, 4) (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
  EXPECT_NE(g->gate_delay_decay, nullptr);
}

TEST(PrimitiveInstantiationParsing, CmosSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  cmos (out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(PrimitiveInstantiationParsing, GateInst_AllCmosSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  cmos  c1(o, i, n, p);\n"
              "  rcmos rc1(o, i, n, p);\n"
              "endmodule\n"));
}

TEST(CmosSwitches, CmosAndRcmos) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire out, in, nctrl, pctrl;\n"
              "  cmos  g1(out, in, nctrl, pctrl);\n"
              "  rcmos g2(out, in, nctrl, pctrl);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_PulldownBasic) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(PrimitiveInstantiationParsing, GateInst_PullupBasic) {
  auto r = Parse(
      "module m;\n"
      "  pullup (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(PrimitiveInstantiationParsing, PullGateInst_PullupNamed) {
  auto r = Parse(
      "module m;\n"
      "  pullup pu1(net1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pu1");
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(PrimitiveInstantiationParsing, PullGateInst_PulldownNamed) {
  auto r = Parse(
      "module m;\n"
      "  pulldown pd1(net1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pd1");
  EXPECT_EQ(g->gate_terminals.size(), 1u);
}

TEST(PrimitiveInstantiationParsing, PullGateInst_PullupUnnamed) {
  auto r = Parse(
      "module m;\n"
      "  pullup (net1);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(PullSources, PullupAndPulldown) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b;\n"
              "  pullup   g1(a);\n"
              "  pulldown g2(b);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_CmosMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(o1, i1, n1, p1), c2(o2, i2, n2, p2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->gate_inst_name, "c1");
  EXPECT_EQ(gates[1]->gate_inst_name, "c2");
}

TEST(PrimitiveInstantiationParsing, GateInst_MosMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pmos p1(o1, i1, c1), p2(o2, i2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, GateInst_EnableMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 b1(o1, i1, c1), b2(o2, i2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, GateInst_NInputMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  and a1(o1, i1, i2), a2(o2, i3, i4);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->gate_inst_name, "a1");
  EXPECT_EQ(gates[1]->gate_inst_name, "a2");
}

TEST(PrimitiveInstantiationParsing, GateInst_NOutputMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(o1, i1), b2(o2, i2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, GateInst_PassEnMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 t1(a1, b1, c1), t2(a2, b2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, GateInst_PassSwitchMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  tran t1(a1, b1), t2(a2, b2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, GateInst_PulldownMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(PrimitiveInstantiationParsing, GateInst_PullupMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pullup pu1(a), pu2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

TEST(GateInstantiationParsing, GateInst_WithStrengthAndDelay) {
  auto r = Parse("module m; and (strong0, weak1) #5 g(y, a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, GateInst_EnableWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (strong0, pull1) b1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(PrimitiveInstantiationParsing, GateInst_NInputWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  and (pull0, pull1) a1(out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(PrimitiveInstantiationParsing, GateInst_NOutputWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  buf (strong0, strong1) b1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(PrimitiveInstantiationParsing, GateInst_StrengthOrder_Strength1First) {
  auto r = Parse(
      "module m;\n"
      "  and (pull1, strong0) a1(out, in1, in2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(PrimitiveInstantiationParsing, GateInst_SharedStrengthAcrossInstances) {
  auto r = Parse(
      "module m;\n"
      "  and (weak0, weak1) a1(o1, i1, i2), a2(o2, i3, i4);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, gates[1]->drive_strength0);
  EXPECT_EQ(gates[0]->drive_strength1, gates[1]->drive_strength1);
}

TEST(PrimitiveInstantiationParsing, GateInst_EnableWithStrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 (weak0, weak1) #7 b1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(PrimitiveInstantiationParsing, GateInst_NOutputWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  not #(4, 6) n1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
}

TEST(PrimitiveInstantiationParsing, GateInst_SharedDelayAcrossInstances) {
  auto r = Parse(
      "module m;\n"
      "  or #5 o1(out1, a, b), o2(out2, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_NE(gates[0]->gate_delay, nullptr);
  EXPECT_NE(gates[1]->gate_delay, nullptr);
}

TEST(GateDelayParsing, MultipleInstancesWithRiseFallDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y1, y2, a, b;\n"
      "  and #(4, 6) g1(y1, a, b), g2(y2, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* g1 = r.cu->modules[0]->items[4];
  auto* g2 = r.cu->modules[0]->items[5];
  ASSERT_NE(g1->gate_delay, nullptr);
  EXPECT_EQ(g1->gate_delay->int_val, 4u);
  ASSERT_NE(g1->gate_delay_fall, nullptr);
  EXPECT_EQ(g1->gate_delay_fall->int_val, 6u);
  ASSERT_NE(g2->gate_delay, nullptr);
  EXPECT_EQ(g2->gate_delay->int_val, 4u);
  ASSERT_NE(g2->gate_delay_fall, nullptr);
  EXPECT_EQ(g2->gate_delay_fall->int_val, 6u);
}

TEST(GateDelayParsing, MintypMaxDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #(1:2:3) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->kind, ExprKind::kMinTypMax);
}

TEST(PrimitiveInstantiationParsing, GateInst_DelayWithMinTypMax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and #(1:2:3, 4:5:6) a1(out, in1, in2);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInst_EnableWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  notif1 #(3, 4, 5) (out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
  EXPECT_NE(g->gate_delay_decay, nullptr);
}

TEST(PrimitiveInstantiationParsing, GateInst_PulldownNamed) {
  auto r = Parse(
      "module m;\n"
      "  pulldown pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pd1");
}

TEST(PrimitiveInstantiationParsing, GateInst_PullupNamed) {
  auto r = Parse(
      "module m;\n"
      "  pullup pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "pu1");
}

TEST(PrimitiveInstantiationParsing, CmosSwitchInst_Named) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "c1");
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(PrimitiveInstantiationParsing, CmosSwitchInst_RcmosNamed) {
  auto r = Parse(
      "module m;\n"
      "  rcmos rc1(out, in, nctrl, pctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rc1");
}

TEST(PrimitiveInstantiationParsing, GateInst_NamedUnnamedMixedInMulti) {
  auto r = Parse(
      "module m;\n"
      "  and a1(o1, i1, i2), a2(o2, i3, i4), a3(o3, i5, i6);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 3u);
  EXPECT_EQ(gates[0]->gate_inst_name, "a1");
  EXPECT_EQ(gates[1]->gate_inst_name, "a2");
  EXPECT_EQ(gates[2]->gate_inst_name, "a3");
}

// --- Error conditions ---

TEST(PrimitiveInstantiationParsing, Error_MissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  and a1(o, i1, i2)\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_MissingClosingParen) {
  auto r = Parse(
      "module m;\n"
      "  and a1(o, i1, i2;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_StrengthOnMosSwitch) {
  auto r = Parse(
      "module m;\n"
      "  nmos (strong0, weak1) n1(o, i, g);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_StrengthOnCmosSwitch) {
  auto r = Parse(
      "module m;\n"
      "  cmos (pull0, pull1) c1(o, i, n, p);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_StrengthOnPassSwitch) {
  auto r = Parse(
      "module m;\n"
      "  tran (strong0, strong1) t1(a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_StrengthOnPassEnSwitch) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (strong0, strong1) t1(a, b, c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_DelayOnPassSwitch) {
  auto r = Parse(
      "module m;\n"
      "  tran #5 t1(a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_DelayOnPullup) {
  auto r = Parse(
      "module m;\n"
      "  pullup #5 pu1(net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_DelayOnPulldown) {
  auto r = Parse(
      "module m;\n"
      "  pulldown #5 pd1(net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_ThreeValueDelayOnNInputGate) {
  auto r = Parse(
      "module m;\n"
      "  and #(1, 2, 3) a1(o, i1, i2);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_ThreeValueDelayOnNOutputGate) {
  auto r = Parse(
      "module m;\n"
      "  buf #(1, 2, 3) b1(o, i);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_PullGateTooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  pullup (a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_PassSwitchTooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  tran (a, b, c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_CmosSwitchTooFewTerminals) {
  auto r = Parse(
      "module m;\n"
      "  cmos c1(o, i, n);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_EnableGateTooFewTerminals) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (o, i);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_NInputGateSingleTerminal) {
  auto r = Parse(
      "module m;\n"
      "  and (o);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// --- Delay coverage ---

TEST(PrimitiveInstantiationParsing, GateInst_NOutputSingleDelay) {
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

TEST(PrimitiveInstantiationParsing, GateInst_PassEnSingleDelay) {
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

TEST(PrimitiveInstantiationParsing, Error_PassEnThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 #(2, 4, 6) t1(a, b, c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, GateInst_MosTwoValueDelay) {
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

TEST(PrimitiveInstantiationParsing, GateInst_MosThreeValueDelay) {
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

TEST(PrimitiveInstantiationParsing, GateInst_CmosTwoValueDelay) {
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

// --- Structural coverage ---

TEST(PrimitiveInstantiationParsing, AllNineAlternativesInOneModule) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and   a1(o, i1, i2);\n"
              "  buf   b1(o, i);\n"
              "  bufif0 bf1(o, i, c);\n"
              "  nmos  n1(o, i, g);\n"
              "  cmos  c1(o, i, n, p);\n"
              "  tran  t1(a, b);\n"
              "  tranif0 tf1(a, b, c);\n"
              "  pullup  pu1(net1);\n"
              "  pulldown pd1(net2);\n"
              "endmodule\n"));
}

TEST(PrimitiveInstantiationParsing, GateInGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    genvar i;\n"
      "    for (i = 0; i < 4; i = i + 1) begin\n"
      "      and a1(o[i], a[i], b[i]);\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
