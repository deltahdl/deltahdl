#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ChargeDecaySpecParsing, ThreeDelayPositionsAreRiseFallDecay) {
  auto r = Parse(
      "module t;\n"
      "  trireg #(7, 11, 13) cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 7u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 11u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 13u);
}

TEST(ChargeDecaySpecParsing, SingleDelayIsNotChargeDecay) {
  auto r = Parse(
      "module t;\n"
      "  trireg #50 cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 50u);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(ChargeDecaySpecParsing, TwoDelaysLeaveChargeDecayUnspecified) {
  auto r = Parse(
      "module t;\n"
      "  trireg #(4, 9) cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 4u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 9u);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

}
