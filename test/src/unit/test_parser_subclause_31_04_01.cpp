#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, SkewBasic) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk1, negedge clk2, 3);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, SkewWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk1, negedge clk2, 3, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, SkewLimitIsExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tSkew = 5;\n"
      "  $skew(posedge clk, data, tSkew);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  ASSERT_EQ(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, SkewRejectsTrailingArgument) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk, data, 5, ntfr, extra);\n"
      "endspecify\n"
      "endmodule\n");
  // $skew takes no argument past the notifier, so the argument list has to
  // close there; the shared timing-check parser reports under §31.2.
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ','", 3, "31.2"));
}

TEST(TimingCheckCommandParsing, SkewWithoutEdgeControls) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(clk1, clk2, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
}

// Syntax 31-9 spells the trailing argument as [ , [ notifier ] ]: the comma
// may appear with the notifier itself omitted. A bare trailing comma must
// parse cleanly and leave the notifier empty.
TEST(TimingCheckCommandParsing, SkewAcceptsTrailingCommaWithoutNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk, d, 5,);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, SkewMissingLimitIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew(posedge clk, d);\n"
      "endspecify\n"
      "endmodule\n");
  // The shared timing-check parser files the missing separator under §31.2, the
  // system_timing_check production, rather than under §31.4.1.
  EXPECT_TRUE(ReportedError(r.diags, "expected ',', got ')'", 3, "31.2"));
}

TEST(TimingCheckCommandParsing, SkewEmptyArgListIsError) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $skew();\n"
      "endspecify\n"
      "endmodule\n");
  // The reference_event's specify_terminal_descriptor is missing, and the
  // shared terminal parser files that under §30.4.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ')'", 3, "30.4"));
}

}  // namespace
