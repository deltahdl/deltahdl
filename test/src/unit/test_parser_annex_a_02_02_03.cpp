#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DelayParsing, DelayValueUnsignedNumber) {
  auto r = Parse(
      "module m;\n"
      "  wire #10 w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(item->net_delay->int_val, 10u);
}

TEST(DelayParsing, DelayValueRealNumber) {
  auto r = Parse(
      "module m;\n"
      "  wire #1.5 w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kRealLiteral);
}

TEST(DelayParsing, Delay3NetTwoValues) {
  auto r = Parse(
      "module m;\n"
      "  wire #(10, 20) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 10u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 20u);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(DelayParsing, Delay3NetThreeValues) {
  auto r = Parse(
      "module m;\n"
      "  wire #(10, 20, 30) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 10u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 20u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 30u);
}

TEST(DelayParsing, Delay3GateSingleValue) {
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

TEST(DelayParsing, Delay3GateTwoValues) {
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

TEST(DelayParsing, Delay2NInputGateSingleValue) {
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

TEST(DelayParsing, NoDelayDefault) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(DelayParsing, DelayValueTimeLiteral) {
  auto r = Parse(
      "module m;\n"
      "  wire #10ns w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kTimeLiteral);
}

TEST(DelayParsing, DelayValuePsIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  parameter d = 5;\n"
      "  wire #d w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kIdentifier);
}

TEST(DelayParsing, Delay2ParenSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xor #(8) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 8u);
  EXPECT_EQ(item->gate_delay_fall, nullptr);
}

TEST(DelayParsing, Delay2ParenTwoValues) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xor #(10, 20) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 10u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 20u);
}

TEST(DelayParsing, Delay3ParenSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire #(15) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 15u);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(DelayParsing, Delay3MintypMaxExpression) {
  auto r = Parse(
      "module m;\n"
      "  wire #(1:2:3) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kMinTypMax);
}

TEST(DelayParsing, Delay3GateThreeValues) {
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

TEST(DelayParsing, DelayValueOneStep) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign #1step w = 1'b0;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->text, "1step");
}

TEST(DelayParsing, TriregSingleDelay) {
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

TEST(DelayParsing, TriregSingleDelayNoFallDecay) {
  auto r = Parse(
      "module t;\n"
      "  trireg #5 t1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(DelayParsing, Delay3TriregWithChargeStrengthSmall) {
  auto r = Parse(
      "module t;\n"
      "  trireg (small) #(5, 10, 15) cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 1);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 10u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 15u);
}

TEST(DelayParsing, Delay3TriregWithChargeStrengthLarge) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) #(10, 20, 50) cap1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.charge_strength, 4);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 10u);
}

TEST(DelayParsing, Delay3TriregFallAndDecay) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) #(10, 20, 50) cap1;\n"
      "endmodule\n");
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 20u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 50u);
}

// --- delay2: mintypmax in both positions ---

TEST(DelayParsing, Delay2MintypMaxTwoValues) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xor #(1:2:3, 4:5:6) g(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->kind, ExprKind::kMinTypMax);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->kind, ExprKind::kMinTypMax);
}

// --- delay3: mintypmax in all three positions ---

TEST(DelayParsing, Delay3MintypMaxThreeValues) {
  auto r = Parse(
      "module m;\n"
      "  wire #(1:2:3, 4:5:6, 7:8:9) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kMinTypMax);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->kind, ExprKind::kMinTypMax);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->kind, ExprKind::kMinTypMax);
}

}  // namespace
