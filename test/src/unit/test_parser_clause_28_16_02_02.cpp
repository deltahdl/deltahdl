// §28.16.2.2: Delay specification for charge decay time

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §6.7.1: Trireg with charge strength and delay combined.
TEST(ParserSection6, Sec6_7_1_TriregChargeStrengthWithDelay) {
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
TEST(ParserSection6, TriregThreeDelay_Strength) {
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

TEST(ParserSection6, TriregThreeDelay_FallAndDecay) {
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

}  // namespace
