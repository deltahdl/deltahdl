#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DelayParsing, SingleDelayOnContAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire out, in;\n"
      "  assign #5 out = in;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 5u);
  EXPECT_EQ(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay_decay, nullptr);
}

TEST(DelayParsing, RiseFallDecayDelaysOnContAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire out, in;\n"
      "  assign #(10, 20, 30) out = in;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 10u);
  ASSERT_NE(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay_fall->int_val, 20u);
  ASSERT_NE(item->assign_delay_decay, nullptr);
  EXPECT_EQ(item->assign_delay_decay->int_val, 30u);
}

TEST(DelayParsing, ParenthesizedSingleDelayOnContAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire out, in;\n"
      "  assign #(5) out = in;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 5u);
}
TEST(ContinuousAssignSyntaxParsing, RiseFallDelayFieldsOnContAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_NE(cas[0]->assign_delay_fall, nullptr);
  EXPECT_EQ(cas[0]->assign_delay_decay, nullptr);
}

TEST(DelayParsing, RiseFallDelayValuesOnContAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire out, in;\n"
      "  assign #(10, 20) out = in;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->int_val, 10u);
  ASSERT_NE(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay_fall->int_val, 20u);
  EXPECT_EQ(item->assign_delay_decay, nullptr);
}

TEST(ContAssignDelayParsing, WireDelayWithInit) {
  auto r = Parse(
      "module t;\n"
      "  wire #3 w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 3u);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ContAssignDelayParsing, NetDeclThreeDelayWithInit) {
  auto r = Parse(
      "module t;\n"
      "  wire #(3, 6, 9) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 3u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 6u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 9u);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ContAssignDelayParsing, NetDeclTwoDelayWithInit) {
  auto r = Parse(
      "module t;\n"
      "  wire #(5, 10) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 10u);
  EXPECT_EQ(item->net_delay_decay, nullptr);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ContAssignDelayParsing, VectorNetDeclWithDelay) {
  auto r = Parse(
      "module t;\n"
      "  wire #(5, 10) [7:0] w = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 10u);
}

}  // namespace
