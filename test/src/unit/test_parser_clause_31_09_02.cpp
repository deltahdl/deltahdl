#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, SetupholdTimestampCondMinTypMax) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->timestamp_cond, nullptr);
  EXPECT_EQ(tc->timestamp_cond->kind, ExprKind::kMinTypMax);
}

TEST(TimingCheckCommandParsing, SetupholdTimecheckCondMinTypMax) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->timecheck_cond, nullptr);
  EXPECT_EQ(tc->timecheck_cond->kind, ExprKind::kMinTypMax);
}

TEST(TimingCheckCommandParsing, RecremTimecheckCondMinTypMax) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, 3, ntfr, 1:2:3, 4:5:6);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_NE(tc->timestamp_cond, nullptr);
  ASSERT_NE(tc->timecheck_cond, nullptr);
}

TEST(TimingCheckCommandParsing, SetupholdOmittedTimestampPopulatedTimecheck) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge CP, D, -10, 20, notifier, , TE_cond_D,"
      " dCP, dD);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->timestamp_cond, nullptr);
  ASSERT_NE(tc->timecheck_cond, nullptr);
  EXPECT_EQ(tc->delayed_ref, "dCP");
  EXPECT_EQ(tc->delayed_data, "dD");
}

}
