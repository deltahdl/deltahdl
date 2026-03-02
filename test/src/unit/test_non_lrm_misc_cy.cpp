// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection28, GateMinTypMaxDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  bufif0 #(5:7:9, 8:10:12, 15:18:21) b1(io1, io2, dir);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_NE(item->gate_delay, nullptr);
}

// delay3: three values on gate (rise, fall, turn-off).
TEST(ParserA223, Delay3GateThreeValues) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire y, a, b;\n"
      "  bufif1 #(10, 20, 30) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 10u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 20u);
  ASSERT_NE(item->gate_delay_decay, nullptr);
  EXPECT_EQ(item->gate_delay_decay->int_val, 30u);
}

}  // namespace
