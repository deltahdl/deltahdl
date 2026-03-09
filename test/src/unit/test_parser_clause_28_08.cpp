#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_Tranif0Basic) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_Tranif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tranif1 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Rtranif0Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif0 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_Rtranif1Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtranif1 (io1, io2, ctrl);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_PassEnWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 #(3, 5) t1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(ParserA301, GateInst_TranBasic) {
  auto r = Parse(
      "module m;\n"
      "  tran (io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, GateInst_RtranBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  rtran (io1, io2);\n"
              "endmodule\n"));
}

TEST(ParserA301, PassSwitchInst_TranNamed) {
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

TEST(ParserA301, PassSwitchInst_RtranNamed) {
  auto r = Parse(
      "module m;\n"
      "  rtran rt1(io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(ParserA301, PassSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  tran (io1, io2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(ParserA301, PassEnSwitchInst_Tranif0Named) {
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

TEST(ParserA301, PassEnSwitchInst_Tranif1Named) {
  auto r = Parse(
      "module m;\n"
      "  tranif1 t1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "t1");
}

TEST(ParserA301, PassEnSwitchInst_Rtranif0Named) {
  auto r = Parse(
      "module m;\n"
      "  rtranif0 rt1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(ParserA301, PassEnSwitchInst_Rtranif1Named) {
  auto r = Parse(
      "module m;\n"
      "  rtranif1 rt1(io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "rt1");
}

TEST(ParserA301, PassEnSwitchInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (io1, io2, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

TEST(ParserA301, GateInst_AllPassSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tran  t1(a, b);\n"
              "  rtran rt1(a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_AllPassEnSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tranif0  t0(a, b, c);\n"
              "  tranif1  t1(a, b, c);\n"
              "  rtranif0 rt0(a, b, c);\n"
              "  rtranif1 rt1(a, b, c);\n"
              "endmodule\n"));
}

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
