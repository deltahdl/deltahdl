#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(NetDelayParsing, NetWithThreeDelayValuesPopulatesAllSlots) {
  // A wire declaration can carry rise, fall, and turn-off slots; the parser
  // routes each into its dedicated AST field.
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
  // No delay specification on a net leaves every delay slot empty; the
  // downstream stages then carry zero propagation through this net.
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
  // §28.16 caps a net at three delay values (rise, fall, turn-off). A fourth
  // value in the delay list is outside the grammar and the parser reports an
  // error rather than accepting it.
  auto r = Parse(
      "module m;\n"
      "  wire #(1, 2, 3, 4) w;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(NetDelayParsing, GateWithMoreThanThreeDelayValuesIsRejected) {
  // §28.16 caps a gate output at three delay values as well. A tristate gate
  // accepts up to three (rise, fall, turn-off); a fourth value in the list is
  // rejected by the parser.
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  reg d, en;\n"
      "  bufif1 #(1, 2, 3, 4) g(y, d, en);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
