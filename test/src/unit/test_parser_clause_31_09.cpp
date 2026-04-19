#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.9: the allowance for negative values in $setuphold originates
// here, not in §31.3.3. Exercising both limit slots simultaneously
// proves the parser carries the unary minus through each slot in one
// go, which subsumes the two single-slot permutations.
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

// §31.9: $recrem inherits the same "negative values are allowed" rule
// as $setuphold; a negative recovery_limit must parse cleanly.
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

// §31.9: mirror for $recrem — a negative removal_limit must parse
// cleanly, matching the identical-behaviour rule the main clause
// states for $setuphold and $recrem.
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

}  // namespace
