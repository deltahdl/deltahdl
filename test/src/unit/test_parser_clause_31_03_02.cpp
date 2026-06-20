#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.3.2 owns Syntax 31-4, the $hold_timing_check production:
//   $hold ( reference_event , data_event , timing_check_limit [ , [ notifier ]
//   ] ) ;
// The shared timing-check parser (ParseTimingCheck / ParseTimingCheckKind /
// ParseTimingCheckTrailingArgs) carries it. The terminals are recorded
// positionally, so for $hold the first argument (the reference_event) lands in
// ref_terminal and the second (the data_event) in data_terminal -- the reverse
// of the $setup ordering in §31.3.1. The timestamp/timecheck role assignment of
// Table 31-2 is applied later by the simulator. The optional trailing notifier
// (notifier ::= variable_identifier) is the same notifier whose
// violation-response semantics §31.6 defines.

TEST(TimingCheckCommandParsing, HoldParsesReferenceDataLimit) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $hold(posedge clk, d, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kHold);
  // First positional argument is the reference_event.
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  // Second positional argument is the data_event.
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->timing_check.data_terminal.name, "d");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
  // The optional notifier is omitted here, so nothing is recorded for it.
  EXPECT_TRUE(si->timing_check.notifier.empty());
}

TEST(TimingCheckCommandParsing, HoldNotifierIsOptionalLastArgument) {
  // The trailing notifier (see §31.6) is the optional last argument of the
  // $hold syntax; when present, the parser records the variable identifier.
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data, 5, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kHold);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, HoldAcceptsTrailingCommaWithoutNotifier) {
  // Syntax 31-4's optional [ , [ notifier ] ] also permits the separating
  // comma to appear with the notifier itself omitted; the parser accepts this
  // and records no notifier (the trailing-comma branch of the trailing-arg
  // loop, distinct from the no-comma and comma+notifier forms).
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data, 5, );\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kHold);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, HoldLimitIsExpression) {
  // timing_check_limit ::= expression, so a specparam is accepted as the limit.
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tHold = 5;\n"
      "  $hold(posedge clk, data, tHold);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kHold);
  ASSERT_EQ(tc->limits.size(), 1u);
}

}  // namespace
