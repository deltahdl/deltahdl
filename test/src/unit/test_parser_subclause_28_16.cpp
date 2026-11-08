#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(NetDelayParsing, NetWithThreeDelayValuesPopulatesAllSlots) {
  auto r = Parse(
      "module m;\n"
      "  wire #(3, 5, 9) w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  ASSERT_NE(item->net_delay_fall, nullptr);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 3u);
  EXPECT_EQ(item->net_delay_fall->int_val, 5u);
  EXPECT_EQ(item->net_delay_decay->int_val, 9u);
}

TEST(NetDelayParsing, NetWithTwoDelayValuesLeavesDecayNull) {
  auto r = Parse(
      "module m;\n"
      "  wire #(2, 4) w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 2u);
  EXPECT_EQ(item->net_delay_fall->int_val, 4u);
}

TEST(NetDelayParsing, NetWithSingleDelayLeavesFallAndDecayNull) {
  auto r = Parse(
      "module m;\n"
      "  wire #6 w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 6u);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(NetDelayParsing, NetWithoutDelaySpecLeavesAllSlotsNull) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

TEST(NetDelayParsing, NetWithMoreThanThreeDelayValuesIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire #(1, 2, 3, 4) w;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ','", 2, "28.16"));
}

TEST(NetDelayParsing, GateWithMoreThanThreeDelayValuesIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  reg d, en;\n"
      "  bufif1 #(1, 2, 3, 4) g(y, d, en);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ','", 4, "28.16"));
}

}  // namespace
