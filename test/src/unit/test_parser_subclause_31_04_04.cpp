#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandParsing, WidthFullForm) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, 1, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, WidthMinimalForm) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, WidthNoDataSignal) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, 1);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  EXPECT_TRUE(tc->data_terminal.name.empty());
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
}

TEST(TimingCheckCommandParsing, WidthThirdArgIsThresholdNotNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, gate);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limits.size(), 2u);
  EXPECT_TRUE(tc->notifier.empty());
}

TEST(TimingCheckCommandParsing, ErrorWidthNotifierWithoutThreshold) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, , ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 3, "11.2"));
}

TEST(TimingCheckCommandParsing, ErrorWidthReferenceMissingEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "$width reference_event must be an edge specification", 3,
      "31.4.4"));
}

TEST(TimingCheckCommandParsing, WidthNegedgeReferenceAccepted) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(negedge clr, 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->ref_terminal.name, "clr");
}

TEST(TimingCheckCommandParsing, WidthEdgeControlReferenceAccepted) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(edge[01] clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kEdge);
}

TEST(TimingCheckCommandParsing, ErrorWidthMissingLimit) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ',', got ')'", 3, "31.2"));
}

}  // namespace
