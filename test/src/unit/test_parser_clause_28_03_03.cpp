#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

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

TEST(GateDelayParsing, PullupDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  pullup #5 pu1(net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GateDelayParsing, PulldownDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  pulldown #5 pd1(net1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GateDelayParsing, NInputGateThreeValueDelayRejected) {
  auto r = Parse(
      "module m;\n"
      "  and #(1, 2, 3) a1(o, i1, i2);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DelayParsing, AndGateSingleValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #5 g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 5u);
  EXPECT_EQ(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_decay, nullptr);
}

TEST(DelayParsing, AndGateTwoValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and #(10, 20) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 10u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 20u);
  EXPECT_EQ(item->gate_delay_decay, nullptr);
}

TEST(DelayParsing, XorGateSingleValueDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xor #7 g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 7u);
}

// When no `#` appears, all three delay fields remain null — the zero-delay
// baseline §28.3.3 permits.
TEST(GateDelayParsing, GateWithoutDelayHasNullDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  and g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_delay, nullptr);
  EXPECT_EQ(g->gate_delay_fall, nullptr);
  EXPECT_EQ(g->gate_delay_decay, nullptr);
}

}  // namespace
