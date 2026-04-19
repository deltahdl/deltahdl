#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.8: a vector data terminal — the LRM example's `$setup(DAT, posedge
// CLK, 10)` with an 8-bit DAT — parses without diagnostics and lands a
// data terminal whose name matches the vector signal.
TEST(VectorSignalsInTimingChecks, SetupVectorDataTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(DAT, posedge CLK, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.name, "DAT");
}

// §31.8: "Either or both signals" — a vector reference terminal alongside
// a vector data terminal exercises the both-signals-vector arm of the
// rule. The parser must accept both terminals as part-selects.
TEST(VectorSignalsInTimingChecks, SetupBothVectorTerminalsParse) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk[1:0], data[7:0], 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kPartSelect);
}

// §31.8: the plus-indexed part-select form `[base+:width]` is a valid
// vector terminal. The parser tags it accordingly so the vector-width
// extraction in later stages can derive the bit count.
TEST(VectorSignalsInTimingChecks, SetupPlusIndexedDataTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[0+:8], posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kPlusIndexed);
}

// §31.8: the minus-indexed part-select form `[base-:width]` is the
// fourth vector terminal grammar form and must parse identically to the
// plus-indexed form.
TEST(VectorSignalsInTimingChecks, SetupMinusIndexedDataTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[7-:8], posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kMinusIndexed);
}

// §31.8: a single-signal timing check ($width) accepts a vector
// reference terminal. The vector applies to the only signal the check
// names, so the per-bit expansion mode would yield N independent checks.
TEST(VectorSignalsInTimingChecks, WidthVectorReferenceTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge rst[3:0], 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kPartSelect);
}

// §31.8: $period is the second single-signal check the LRM names
// alongside $width. A vector reference terminal must parse here as well.
TEST(VectorSignalsInTimingChecks, PeriodVectorReferenceTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk[1:0], 100);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kPartSelect);
}

// §31.8: the LRM enumerates ten two-signal timing checks that admit
// vector terminals. $nochange is the last entry in that enumeration and
// is exercised here with a vector data terminal.
TEST(VectorSignalsInTimingChecks, NochangeVectorDataTerminalParses) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $nochange(posedge clk, data[7:0], 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kNochange);
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kPartSelect);
}

}  // namespace
