// §28.5

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BufNotParsing, SingleTerminalRejected) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BufNotParsing, MinimumTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  not (out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(BufNotParsing, NamedBufGateParses) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBuf);
  EXPECT_EQ(item->gate_inst_name, "b1");
  ASSERT_EQ(item->gate_terminals.size(), 2);
}

TEST(BufNotParsing, NamedNotGateParses) {
  auto r = Parse(
      "module m;\n"
      "  not n1(out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNot);
}

TEST(BufNotParsing, GateBufMultiOutput) {
  auto r = Parse("module t; buf (o1, o2, in); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kBuf);
  EXPECT_TRUE(item->gate_inst_name.empty());
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

// §28.5: buf/not delay spec is capped at two delays (delay2); three delays
// are rejected.
TEST(BufNotParsing, ThreeValueDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  buf #(1, 2, 3) b1(o, i);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §28.5: single-delay form is accepted; the one value becomes both the
// rise and fall delay for the gate.
TEST(BufNotParsing, SingleValueDelay) {
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

// §28.5: two delays express distinct rise and fall values; both must be
// captured.
TEST(BufNotParsing, TwoValueDelayAccepted) {
  auto r = Parse(
      "module m;\n"
      "  not #(2, 7) n1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  ASSERT_NE(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay->int_val, 2u);
  ASSERT_NE(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_fall->int_val, 7u);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

}  // namespace
