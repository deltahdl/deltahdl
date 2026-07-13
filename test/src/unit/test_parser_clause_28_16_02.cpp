#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ChargeDecayParsing, TriregNoDelayIdeal) {
  auto r = Parse(
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(ChargeDecayParsing, ThreeDelaysSlotIntoRiseFallDecay) {
  auto r = Parse(
      "module t;\n"
      "  trireg #(3, 5, 9) cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 3u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 5u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 9u);
}

// §28.16.2: a trireg net declaration can contain up to three delays. With a
// single delay, only the rise/transition delay slot is filled; there is no fall
// delay and no charge decay time.
TEST(ChargeDecayParsing, OneDelayFillsRiseOnly) {
  auto r = Parse(
      "module t;\n"
      "  trireg #(4) cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 4u);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// §28.16.2: with two delays the first two slots (the 1 and 0 transition delays)
// are filled, but no third delay is present, so there is no charge decay time
// -- the decay slot stays empty. This is the boundary that distinguishes a
// decaying trireg from one whose stored charge is ideal.
TEST(ChargeDecayParsing, TwoDelaysGiveRiseAndFallNoDecay) {
  auto r = Parse(
      "module t;\n"
      "  trireg #(3, 5) cap;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 3u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 5u);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// §28.16.2 negative form: a trireg accepts at most three delays. A fourth delay
// term exceeds that limit and is rejected as a syntax error.
TEST(ChargeDecayParsing, MoreThanThreeDelaysRejected) {
  auto r = Parse(
      "module t;\n"
      "  trireg #(1, 2, 3, 4) cap;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
