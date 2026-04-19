#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.9.2: the sixth positional argument of $setuphold is the
// timestamp_condition introduced by this subclause, and the parser
// must capture it as a mintypmax-kind expression when written in that
// form.
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

// §31.9.2: the seventh positional argument is the timecheck_condition,
// and both condition slots must populate independently when the pair
// is written out.
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

// §31.9.2: the LRM is explicit that "the behaviour of these two timing
// checks is identical", so $recrem must accept the same two condition
// slots that $setuphold does.
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

// §31.9.2 example 1 on page 922: the specific syntax that associates
// the timecheck condition with the data signal via an empty
// timestamp_condition slot — the parser must accept the comma-first
// form that leaves the sixth argument unset while populating the
// seventh.
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

}  // namespace
