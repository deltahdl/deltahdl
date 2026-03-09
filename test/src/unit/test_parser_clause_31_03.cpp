#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection28, Sec28_12_MultipleTimingChecksInSpecifyBlock) {
  auto r = Parse(
      "module m(input d, clk, rst);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "    $hold(posedge clk, d, 3);\n"
      "    $recovery(posedge clk, rst, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kSetup);
  EXPECT_EQ(spec->specify_items[1]->timing_check.check_kind,
            TimingCheckKind::kHold);
  EXPECT_EQ(spec->specify_items[2]->timing_check.check_kind,
            TimingCheckKind::kRecovery);
}

}  // namespace
