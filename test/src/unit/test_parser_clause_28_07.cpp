// §28.7

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

// --- Terminal count error cases not covered by subsection files ---
TEST(MosSwitchParsing, TooFewTerminals) {
  auto r = Parse(
      "module m;\n"
      "  nmos n1(out, data);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(MosSwitchParsing, TooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  pmos p1(out, data, ctrl, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(MosSwitchParsing, NamedNmosInstantiation) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nmos n1(out, data, control);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_inst_name, "n1");
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(MosSwitchParsing, UnnamedNmosInstantiation) {
  auto r = ParseWithPreprocessor("module t; nmos (out, in, ctrl); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(MosSwitchParsing, NmosAcceptsTwoValueDelay) {
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

TEST(MosSwitchParsing, PmosAcceptsThreeValueDelay) {
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

TEST(MosSwitchParsing, NmosAcceptsThreeValueDelay) {
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

TEST(MosSwitchParsing, RnmosAcceptsThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  rnmos #(1, 2, 3) r1(o, i, g);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRnmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

TEST(MosSwitchParsing, RpmosAcceptsThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  rpmos #(4, 5, 6) r1(o, i, g);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kRpmos);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

TEST(MosSwitchParsing, AllFourKindsParseToDistinctGateKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nmos  (out, in, ctrl);\n"
      "  pmos  (out, in, ctrl);\n"
      "  rnmos (out, in, ctrl);\n"
      "  rpmos (out, in, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 4);
  GateKind expected[] = {GateKind::kNmos, GateKind::kPmos,
                         GateKind::kRnmos, GateKind::kRpmos};
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->items[i]->gate_kind, expected[i]);
  }
}

// The first terminal is the driven output — verifying the identifier text
// pins the (output, data, control) ordering the parser captures.
TEST(MosSwitchParsing, TerminalOrderOutputDataControl) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, en;\n"
      "  nmos n1(y, a, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  ASSERT_EQ(g->gate_terminals.size(), 3u);
  EXPECT_EQ(g->gate_terminals[0]->text, "y");
  EXPECT_EQ(g->gate_terminals[1]->text, "a");
  EXPECT_EQ(g->gate_terminals[2]->text, "en");
}

}  // namespace
