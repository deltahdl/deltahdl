// §31.3.2: $hold

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $hold_timing_check
// =============================================================================
// $hold ( reference_event , data_event , timing_check_limit [ , [ notifier ] ]
// )
TEST(ParserA70501, HoldTimingCheck) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kHold);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_EQ(tc->data_terminal.name, "data");
}

TEST(ParserAnnexA, A7TimingCheckHold) {
  auto r = Parse(
      "module m;\n"
      "  specify $hold(posedge clk, data, 5); endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

using ConfigParseTest = ProgramTestParse;

TEST(ParserSection28, Sec28_12_TimingCheckHold) {
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
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->timing_check.data_terminal.name, "d");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

TimingCheckDecl* GetSoleTimingCheck(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  if (spec->specify_items[0]->kind != SpecifyItemKind::kTimingCheck)
    return nullptr;
  return &spec->specify_items[0]->timing_check;
}

// system_timing_check ::= $hold_timing_check
TEST(ParserA705, SystemTimingCheckHold) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kHold);
}

}  // namespace
