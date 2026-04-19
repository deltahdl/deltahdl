// §28.6

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

// §28.6: tri-state gates require exactly three terminals; fewer must fail
// at parse.
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

// §28.6: zero-delay form (no #spec) is legal and leaves the delay fields
// null.
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

// §28.6: a single delay applies to all transitions; only the rise field
// captures the value.
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

// §28.6: two delays express rise and fall; the turn-off field stays null.
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

// §28.6: delay3 is the cap — four delays must be rejected.
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

TEST(TristateGateParsing, Notif0ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  notif0 #(1, 2, 3) n1(o, i, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

TEST(TristateGateParsing, Bufif0AcceptsThreeDelays) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  bufif0 #(10, 12, 11) b3(out, in, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(TristateGateParsing, Bufif1ThreeValueDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire y, a, b;\n"
      "  bufif1 #(10, 20, 30) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 10u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 20u);
  ASSERT_NE(item->gate_delay_decay, nullptr);
  EXPECT_EQ(item->gate_delay_decay->int_val, 30u);
}

TEST(TristateGateParsing, Notif1ThreeValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  notif1 #(4, 5, 6) n1(o, i, en);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  ASSERT_NE(g->gate_delay_decay, nullptr);
}

}  // namespace
