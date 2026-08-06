

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(TristateGateParsing, TooManyTerminals) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 b1(out, in, en, extra);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TristateGateParsing, SingleTerminalRejected) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 b1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TristateGateParsing, TwoTerminalsRejected) {
  auto r = Parse(
      "module m;\n"
      "  notif1 b1(out, data);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TristateGateParsing, NoDelaySpecLeavesDelayNull) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 b1(o, d, c);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

TEST(TristateGateParsing, SingleValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  bufif1 #5 b1(o, d, c);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 5u);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

TEST(TristateGateParsing, TwoValueDelayAccepted) {
  auto r = Parse(
      "module m;\n"
      "  notif0 #(3, 7) n1(o, d, c);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 3u);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_fall->int_val, 7u);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

TEST(TristateGateParsing, FourValueDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 #(1, 2, 3, 4) b1(o, d, c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(TristateGateParsing, AllFourKindsParseToDistinctGateKind) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  bufif0 (out, in, en);\n"
      "  bufif1 (out, in, en);\n"
      "  notif0 (out, in, en);\n"
      "  notif1 (out, in, en);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 4);
  GateKind expected[] = {GateKind::kBufif0, GateKind::kBufif1,
                         GateKind::kNotif0, GateKind::kNotif1};
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->items[i]->gate_kind, expected[i]);
  }
}

TEST(TristateGateParsing, NamedBufif0Parses) {
  auto r = ParseWithPreprocessor("module t; bufif0 b1(out, in, en); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(TristateGateParsing, Bufif0ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  bufif0 #(5, 10, 15) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 5u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 10u);
  ASSERT_NE(item->gate_delay_decay, nullptr);
  EXPECT_EQ(item->gate_delay_decay->int_val, 15u);
}

}  // namespace
