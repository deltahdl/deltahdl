#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.3.4 owns Syntax 31-6, the $removal_timing_check production:
//   $removal ( reference_event , data_event , timing_check_limit
//             [ , [ notifier ] ] ) ;
// The shared timing-check parser (ParseTimingCheckKind / ParseTimingCheck /
// ParseTimingCheckTrailingArgs) carries it. The terminals are positional, so
// the first argument (the reference_event) lands in ref_terminal and the
// second (the data_event) in data_terminal -- the natural order shared with
// $hold (§31.3.2). The timecheck/timestamp role assignment of Table 31-4 is
// applied later by the simulator. The optional trailing notifier
// (notifier ::= variable_identifier) is the same notifier whose
// violation-response semantics §31.6 defines.

TEST(TimingCheckCommandParsing, RemovalWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $removal(posedge clk, rst, 3, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRemoval);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, RemovalAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $removal(negedge rst, posedge clk, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRemoval);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "rst");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
  // The optional notifier is omitted here, so nothing is recorded for it.
  EXPECT_TRUE(si->timing_check.notifier.empty());
}

TEST(TimingCheckCommandParsing, RemovalAcceptsTrailingCommaWithoutNotifier) {
  // Syntax 31-6's optional [ , [ notifier ] ] also permits the separating
  // comma to appear with the notifier itself omitted; the parser accepts this
  // and records no notifier (the trailing-comma break branch of the
  // trailing-arg loop, distinct from the no-comma and comma+notifier forms).
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $removal(posedge rst, posedge clk, 5, );\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRemoval);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, RemovalLimitIsExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tRem = 3;\n"
      "  $removal(posedge rst, posedge clk, tRem);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRemoval);
  ASSERT_EQ(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, ErrorRemovalMissingLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $removal(posedge rst, posedge clk);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}
