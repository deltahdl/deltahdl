// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Pass/enable switch error for wrong strength/delay combinations ---
TEST(PrimitiveInstantiationParsing, Error_DelayOnTran) {
  auto r = Parse(
      "module m;\n"
      "  tran #5 (a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_DelayOnRtran) {
  auto r = Parse(
      "module m;\n"
      "  rtran #5 (a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveInstantiationParsing, Error_StrengthOnPullGateWrongType) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong0, strong1) (net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// --- Multiple instances with mixed named/unnamed across all types ---
TEST(PrimitiveInstantiationParsing, EnableGateMultipleInstancesMixed) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 b1(o1, a, en), (o2, b, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->gate_inst_name, "b1");
  EXPECT_TRUE(gates[1]->gate_inst_name.empty());
}

TEST(PrimitiveInstantiationParsing, PassEnSwitchMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 t1(a1, b1, en), t2(a2, b2, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
}

// --- Edge case: delay2 vs delay3 ---
TEST(PrimitiveInstantiationParsing, EnableGateAcceptsThreeValueDelay) {
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

TEST(PrimitiveInstantiationParsing, CmosSwitchAcceptsThreeValueDelay) {
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

TEST(PrimitiveInstantiationParsing, MosSwitchAcceptsThreeValueDelay) {
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

TEST(PrimitiveInstantiationParsing, PassEnSwitchAcceptsTwoValueDelay) {
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

// --- Net lvalue validation on output/inout terminals ---
TEST(PrimitiveTerminalParsing, Error_PassSwitchInoutTerminalLiteral) {
  auto r = Parse(
      "module m;\n"
      "  tran (1, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveTerminalParsing, Error_PassEnSwitchInoutTerminalExpr) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (a + b, c, en);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
