// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(GateInstantiationPreprocessor, NOutputGateThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, o1, o2;\n"
      "  buf (o1, o2, a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(GateInstantiationPreprocessor, EnableGateThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif0 b1(y, a, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(GateInstantiationPreprocessor, MosSwitchThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire out, data, ctrl;\n"
      "  nmos n1(out, data, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
}

TEST(GateInstantiationPreprocessor, CmosSwitchThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire out, data, nctrl, pctrl;\n"
      "  cmos c1(out, data, nctrl, pctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(GateInstantiationPreprocessor, PassSwitchThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b;\n"
      "  tran (a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kTran);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(GateInstantiationPreprocessor, PassEnableSwitchThroughPreprocessor) {
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

TEST(GateInstantiationPreprocessor, PullGateThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire net1;\n"
      "  pullup (net1);\n"
      "  pulldown (net1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown),
            nullptr);
}

TEST(GateInstantiationPreprocessor, AllNineAlternativesThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, c, d, o, o2, n1, n2;\n"
      "  and (o, a, b);\n"
      "  buf (o, a);\n"
      "  bufif0 (o, a, b);\n"
      "  nmos (o, a, b);\n"
      "  cmos (o, a, b, c);\n"
      "  tran (n1, n2);\n"
      "  tranif0 (n1, n2, a);\n"
      "  pullup (o);\n"
      "  pulldown (o2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 9u);
}

TEST(GateInstantiationPreprocessor, GateWithMacroExpandedDelay) {
  auto r = ParseWithPreprocessor(
      "`define DELAY 5\n"
      "module m;\n"
      "  wire a, b, y;\n"
      "  and #(`DELAY) g1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(GateInstantiationPreprocessor, GateInsideConditionalCompilation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, y;\n"
      "`ifdef INCLUDE_GATE\n"
      "  and g1(y, a, b);\n"
      "`endif\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd), nullptr);
}

TEST(GateInstantiationPreprocessor, GateWithStrengthAndDelayThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, strong1) #10 g1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);
  EXPECT_EQ(g->drive_strength1, 4u);
  EXPECT_NE(g->gate_delay, nullptr);
}

TEST(GateInstantiationPreprocessor, MultipleInstancesThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, y1, y2;\n"
      "  nand n1(y1, a, b), n2(y2, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 2u);
  for (auto* g : gates) {
    EXPECT_EQ(g->gate_kind, GateKind::kNand);
  }
}

}  // namespace
