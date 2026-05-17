#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(NegativeTimingChecks, SetupholdAcceptsBothNegativeLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, -10, -5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetuphold);
  ASSERT_GE(tc->limits.size(), 2u);
}

TEST(NegativeTimingChecks, RecremAcceptsNegativeRecoveryLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, -8, 3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc->limits.size(), 2u);
}

TEST(NegativeTimingChecks, RecremAcceptsNegativeRemovalLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, -3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
}

}
