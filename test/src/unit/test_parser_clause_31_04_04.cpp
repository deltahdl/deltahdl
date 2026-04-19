#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §31.4.4 Table 31-10: the four-argument form with an explicit threshold
// and a trailing notifier must parse and expose both fields.
TEST(TimingCheckCommandParsing, WidthWithThreshold) {
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

// §31.4.4 Syntax 31-12: the controlled_reference_event carries both an
// edge qualifier and a specify terminal — both must land on the AST.
TEST(TimingCheckCommandParsing, WidthEdgeAndTerminal) {
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
  ASSERT_GE(tc->limits.size(), 1u);
}

// §31.4.4: "Because a data event is not passed to $width, it is derived
// from the reference event" — Syntax 31-12 has no data_event slot, so
// the AST's data terminal/edge remain empty.
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

// §31.4.4 Table 31-10: the threshold argument is a constant_expression,
// captured by the parser as an Expr in the limits slot past the limit.
TEST(TimingCheckCommandParsing, ThresholdExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, 1);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_NE(tc->limits[1], nullptr);
}

// §31.4.4: "It is permissible to not specify both the threshold and
// notifier arguments, making the default value for the threshold zero."
// The bare form omits threshold entirely and must still parse.
TEST(TimingCheckCommandParsing, WidthDefaultThresholdOmitted) {
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
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_TRUE(tc->notifier.empty());
}

// §31.4.4: "An edge triggered event has to be passed as the reference
// event. A compilation error shall occur if the reference event is not
// an edge specification." Bare terminal without posedge/negedge/edge is
// ill-formed.
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
