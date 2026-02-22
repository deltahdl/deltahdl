// Tests for A.7.5.1 — System timing check commands

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

ModuleItem *FindSpecifyBlock(const std::vector<ModuleItem *> &items) {
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock)
      return item;
  }
  return nullptr;
}

TimingCheckDecl *GetSoleTimingCheck(ParseResult &r) {
  if (!r.cu || r.cu->modules.empty())
    return nullptr;
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty())
    return nullptr;
  if (spec->specify_items[0]->kind != SpecifyItemKind::kTimingCheck)
    return nullptr;
  return &spec->specify_items[0]->timing_check;
}

} // namespace

// =============================================================================
// A.7.5.1 $setup_timing_check
// =============================================================================

// $setup ( data_event , reference_event , timing_check_limit [ , [ notifier ] ]
// )
TEST(ParserA70501, SetupTimingCheck) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $setup(data, posedge clk, 10);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->data_terminal.name, "clk");
  ASSERT_EQ(tc->limits.size(), 1u);
}

// $setup with notifier
TEST(ParserA70501, SetupWithNotifier) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $setup(data, posedge clk, 10, ntfr);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
}

// =============================================================================
// A.7.5.1 $hold_timing_check
// =============================================================================

// $hold ( reference_event , data_event , timing_check_limit [ , [ notifier ] ]
// )
TEST(ParserA70501, HoldTimingCheck) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $hold(posedge clk, data, 5);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kHold);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_EQ(tc->data_terminal.name, "data");
}

// =============================================================================
// A.7.5.1 $setuphold_timing_check
// =============================================================================

// $setuphold with two limits
TEST(ParserA70501, SetupholdTwoLimits) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $setuphold(posedge clk, data, 10, 5);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetuphold);
  ASSERT_GE(tc->limits.size(), 2u);
}

// $setuphold with all 9 arguments
TEST(ParserA70501, SetupholdFullArgs) {
  auto r =
      Parse("module m;\n"
            "specify\n"
            "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dDATA);\n"
            "endspecify\n"
            "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  EXPECT_EQ(tc->delayed_data, "dDATA");
}

// =============================================================================
// A.7.5.1 $recovery_timing_check
// =============================================================================

TEST(ParserA70501, RecoveryTimingCheck) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $recovery(posedge clk, rst, 8, ntfr);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecovery);
  EXPECT_EQ(tc->notifier, "ntfr");
}

// =============================================================================
// A.7.5.1 $removal_timing_check
// =============================================================================

TEST(ParserA70501, RemovalTimingCheck) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $removal(posedge clk, rst, 3, ntfr);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRemoval);
  EXPECT_EQ(tc->notifier, "ntfr");
}

// =============================================================================
// A.7.5.1 $recrem_timing_check
// =============================================================================

// $recrem with all 9 arguments
TEST(ParserA70501, RecremFullArgs) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  EXPECT_EQ(tc->delayed_data, "dRST");
}

// =============================================================================
// A.7.5.1 $skew_timing_check
// =============================================================================

TEST(ParserA70501, SkewTimingCheck) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $skew(posedge clk1, negedge clk2, 3, ntfr);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk1");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->data_terminal.name, "clk2");
  EXPECT_EQ(tc->notifier, "ntfr");
}

// =============================================================================
// A.7.5.1 $timeskew_timing_check
// =============================================================================

// $timeskew with event_based_flag and remain_active_flag
TEST(ParserA70501, TimeskewWithFlags) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc->notifier, "ntfr");
  ASSERT_NE(tc->event_based_flag, nullptr);
  ASSERT_NE(tc->remain_active_flag, nullptr);
}

// =============================================================================
// A.7.5.1 $fullskew_timing_check
// =============================================================================

// $fullskew with two limits, event_based_flag and remain_active_flag
TEST(ParserA70501, FullskewWithFlags) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr, 1, 0);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
  ASSERT_NE(tc->event_based_flag, nullptr);
  ASSERT_NE(tc->remain_active_flag, nullptr);
}

// =============================================================================
// A.7.5.1 $period_timing_check
// =============================================================================

// $period ( controlled_reference_event , timing_check_limit [ , [ notifier ] ]
// )
TEST(ParserA70501, PeriodTimingCheck) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $period(posedge clk, 50, ntfr);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_EQ(tc->notifier, "ntfr");
}

// =============================================================================
// A.7.5.1 $width_timing_check
// =============================================================================

// $width ( controlled_reference_event , timing_check_limit , threshold [ , [
// notifier ] ] )
TEST(ParserA70501, WidthWithThreshold) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $width(posedge clk, 20, 1, ntfr);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kWidth);
  ASSERT_GE(tc->limits.size(), 2u);
  EXPECT_EQ(tc->notifier, "ntfr");
}

// =============================================================================
// A.7.5.1 $nochange_timing_check
// =============================================================================

// $nochange with simple integer offsets
TEST(ParserA70501, NochangeTimingCheck) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $nochange(posedge clk, data, 0, 0);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kNochange);
  ASSERT_GE(tc->limits.size(), 2u);
}

// $nochange with notifier
TEST(ParserA70501, NochangeWithNotifier) {
  auto r = Parse("module m;\n"
                 "specify\n"
                 "  $nochange(posedge clk, data, 0, 0, ntfr);\n"
                 "endspecify\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
}
