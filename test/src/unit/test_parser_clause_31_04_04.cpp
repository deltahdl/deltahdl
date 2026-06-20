#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Syntax 31-12: the full $width form carries a reference event, limit,
// threshold and an optional notifier.
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
  ASSERT_GE(tc->limits.size(), 2u);  // limit + threshold
  EXPECT_EQ(tc->notifier, "ntfr");
}

// Syntax 31-12: the minimal form is just a controlled reference event and a
// limit. With both threshold and notifier omitted the threshold defaults
// (no second limit recorded) and the notifier stays empty.
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

// $width derives its data event from the reference event, so no explicit data
// signal is parsed.
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

// A notifier cannot be supplied without a threshold: the first trailing
// argument is always consumed as the threshold, even when it is an identifier
// that would otherwise look like a notifier. This is the parser enforcing that
// the threshold must be present when a notifier is required.
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
  ASSERT_EQ(tc->limits.size(), 2u);  // gate became the threshold
  EXPECT_TRUE(tc->notifier.empty());
}

// Illegal call from the LRM: a notifier with an empty threshold slot. Because
// the threshold position must hold an expression, the empty slot is an error.
TEST(TimingCheckCommandParsing, ErrorWidthNotifierWithoutThreshold) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, , ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// A compilation error is required when the reference event is not an edge
// specification, since the implicit data event is the opposite edge.
TEST(TimingCheckCommandParsing, ErrorWidthReferenceMissingEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
