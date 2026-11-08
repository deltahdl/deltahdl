#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

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

TEST(DelayParsing, Delay2NonParenDelayValue) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  xor #7 g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(item->gate_delay->int_val, 7u);
  EXPECT_EQ(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_decay, nullptr);
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

TEST(DelayParsing, Delay3NetSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire #5 w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(DelayParsing, Delay3OverArityRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire #(1, 2, 3, 4) w;\n"
      "endmodule");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ','", 2, "28.16"));
}

TEST(DelayParsing, ADelayOutsideDelayValueFormsIsReported) {
  auto r = Parse(
      "module m;\n"
      "  assign #D[0] a = b;\n"
      "  and #4'd3 g (c, a, b);\n"
      "  initial #m.D $display(\"x\");\n"
      "  initial #m.D[1] $display(\"y\");\n"
      "  initial #$urandom $display(\"z\");\n"
      "  initial x = #p::q::D y;\n"
      "  initial ->> #$root.D e;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #$unit::C::D data;\n"
      "  endclocking\n"
      "endmodule\n");
  for (uint32_t line : {2u, 3u, 4u, 5u, 6u, 7u, 8u, 10u}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a delay written after '#' without parentheses "
                              "is a number, a real number, a time literal, "
                              "1step or a name behind at most one package "
                              "scope; write this one in parentheses",
                              line, "A.2.2.3"))
        << "line " << line;
  }
}

TEST(DelayParsing, DelayValueFormsAreAccepted) {
  auto r = Parse(
      "package p;\n"
      "  parameter D = 1;\n"
      "endpackage\n"
      "parameter U = 2;\n"
      "module m;\n"
      "  parameter d = 3;\n"
      "  wire #1_0 w1;\n"
      "  wire #5ns w2;\n"
      "  wire #1.5 w3;\n"
      "  wire #d w4;\n"
      "  wire #p::D w5;\n"
      "  wire #$unit::U w6;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DelayParsing, ANameDelayLeavesAnUnnamedGateItsTerminals) {
  auto r = Parse(
      "module m;\n"
      "  parameter d = 2;\n"
      "  wire y, a, b;\n"
      "  and #d (y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* gate = nullptr;
  for (const ModuleItem* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGateInst) gate = item;
  }
  ASSERT_NE(gate, nullptr);
  ASSERT_NE(gate->gate_delay, nullptr);
  EXPECT_EQ(gate->gate_delay->kind, ExprKind::kIdentifier);
  EXPECT_EQ(gate->gate_delay->text, "d");
  EXPECT_EQ(gate->gate_terminals.size(), 3u);
}

}  // namespace
