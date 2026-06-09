#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.3.1 owns Syntax 31-3, the $setup_timing_check production:
//   $setup ( data_event , reference_event , timing_check_limit [ , [ notifier ] ] ) ;
// The shared timing-check parser (ParseTimingCheck / ParseTimingCheckKind /
// ParseTimingCheckTrailingArgs) carries it. The terminals are recorded
// positionally, so for $setup the first argument (the data_event) lands in
// ref_terminal and the second (the reference_event) in data_terminal; the
// timestamp/timecheck role assignment of Table 31-1 is applied later by the
// simulator. The optional trailing notifier (notifier ::= variable_identifier)
// declared in this syntax is the same notifier whose violation-response
// semantics §31.6 defines.

TEST(TimingCheckCommandParsing, SetupParsesDataReferenceLimit) {
  auto sp = ParseSpecifySingle(
      "module m(input data, clk);\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
  // First positional argument is the data_event.
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "data");
  // Second positional argument is the reference_event.
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
  // The optional notifier is omitted here, so nothing is recorded for it.
  EXPECT_TRUE(si->timing_check.notifier.empty());
}

TEST(TimingCheckCommandParsing, SetupNotifierIsOptionalLastArgument) {
  // The trailing notifier (see §31.6) is the optional last argument of the
  // $setup syntax; when present, the parser records the variable identifier.
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, SetupAcceptsTrailingCommaWithoutNotifier) {
  // Syntax 31-3's optional [ , [ notifier ] ] also permits the separating
  // comma to appear with the notifier itself omitted; the parser accepts this
  // and records no notifier (the trailing-comma branch of the trailing-arg
  // loop, distinct from the no-comma and comma+notifier forms).
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10, );\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetup);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, SetupLimitIsExpression) {
  // timing_check_limit ::= expression, so a specparam is accepted as the limit.
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tSetup = 10;\n"
      "  $setup(data, posedge clk, tSetup);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetup);
  ASSERT_EQ(tc->limits.size(), 1u);
}

}
