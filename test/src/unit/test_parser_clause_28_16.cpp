// §28.16: Gate and net delays

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_EnableWithDelay) {
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
// §6.7.1: Net with two delays (rise, fall).
TEST(ParserSection6, Sec6_7_1_WireTwoDelays) {
  auto r = Parse(
      "module t;\n"
      "  wire #(3, 5) w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 3u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 5u);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// §6.7.1: Net with three delays (rise, fall, turnoff).
TEST(ParserSection6, Sec6_7_1_WireThreeDelays) {
  auto r = Parse(
      "module t;\n"
      "  wire #(2, 4, 6) w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 2u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 4u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 6u);
}
TEST(ParserSection6, TriregSingleDelay) {
  auto r = Parse(
      "module t;\n"
      "  trireg #5 t1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
}

TEST(ParserSection6, TriregSingleDelay_NoFallDecay) {
  auto r = Parse(
      "module t;\n"
      "  trireg #5 t1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

}  // namespace
