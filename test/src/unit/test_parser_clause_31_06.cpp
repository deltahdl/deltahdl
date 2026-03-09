#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA70502, NotifierVariable) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST_F(SpecifyTest, TimingCheckWithNotifier) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.notifier, "ntfr");
}

TEST(ParserSection28, Sec28_12_TimingCheckWithNotifier) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  reg notif_reg;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10, notif_reg);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  EXPECT_EQ(sp.sole_item->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(sp.sole_item->timing_check.notifier, "notif_reg");
}

}  // namespace
