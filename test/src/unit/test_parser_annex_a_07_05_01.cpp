#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(SystemTimingCheckParsing, AllTwelveTimingCheckKinds) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "  $hold(posedge clk, data, 5);\n"
      "  $setuphold(posedge clk, data, 10, 5);\n"
      "  $recovery(posedge rst, posedge clk, 10);\n"
      "  $removal(posedge rst, posedge clk, 5);\n"
      "  $recrem(posedge rst, posedge clk, 10, 5);\n"
      "  $skew(posedge clk1, posedge clk2, 50);\n"
      "  $timeskew(posedge clk1, posedge clk2, 50);\n"
      "  $fullskew(posedge clk1, posedge clk2, 50, 50);\n"
      "  $period(posedge clk, 50);\n"
      "  $width(posedge clk, 20, 1);\n"
      "  $nochange(posedge clk, data, 0, 0);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 12u);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kSetup);
  EXPECT_EQ(spec->specify_items[1]->timing_check.check_kind,
            TimingCheckKind::kHold);
  EXPECT_EQ(spec->specify_items[2]->timing_check.check_kind,
            TimingCheckKind::kSetuphold);
  EXPECT_EQ(spec->specify_items[3]->timing_check.check_kind,
            TimingCheckKind::kRecovery);
  EXPECT_EQ(spec->specify_items[4]->timing_check.check_kind,
            TimingCheckKind::kRemoval);
  EXPECT_EQ(spec->specify_items[5]->timing_check.check_kind,
            TimingCheckKind::kRecrem);
  EXPECT_EQ(spec->specify_items[6]->timing_check.check_kind,
            TimingCheckKind::kSkew);
  EXPECT_EQ(spec->specify_items[7]->timing_check.check_kind,
            TimingCheckKind::kTimeskew);
  EXPECT_EQ(spec->specify_items[8]->timing_check.check_kind,
            TimingCheckKind::kFullskew);
  EXPECT_EQ(spec->specify_items[9]->timing_check.check_kind,
            TimingCheckKind::kPeriod);
  EXPECT_EQ(spec->specify_items[10]->timing_check.check_kind,
            TimingCheckKind::kWidth);
  EXPECT_EQ(spec->specify_items[11]->timing_check.check_kind,
            TimingCheckKind::kNochange);
}

TEST(TimingCheckCommandParsing, SetupWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(TimingCheckCommandParsing, SetupEmptyNotifierSlot) {
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
  ASSERT_EQ(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, SetupAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->timing_check.data_terminal.name, "d");
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, NochangeAsSpecifyItem) {
  auto sp = ParseSpecifySingle(
      "module m(input clk, data);\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 0, 0);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kNochange);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_terminal.name, "data");
  ASSERT_GE(si->timing_check.limits.size(), 2u);
}

TEST(TimingCheckCommandParsing, SetupholdTwoLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(tc->data_terminal.name, "data");
  ASSERT_EQ(tc->limits.size(), 2u);
}

TEST(TimingCheckCommandParsing, SetupholdSingleLimitRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "$setuphold requires two timing_check_limit arguments", 3,
      "31.3.3"));
}

TEST(TimingCheckCommandParsing, RecremTwoLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge rst, posedge clk, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
  ASSERT_EQ(tc->limits.size(), 2u);
}

TEST(TimingCheckCommandParsing, RecremSingleLimitRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge rst, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "$recrem requires two timing_check_limit arguments",
                            3, "31.3.6"));
}

TEST(TimingCheckCommandParsing, FullskewTwoLimits) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, posedge clk2, 50, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kFullskew);
  ASSERT_EQ(tc->limits.size(), 2u);
}

TEST(TimingCheckCommandParsing, FullskewSingleLimitRejected) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, posedge clk2, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "$fullskew requires two timing_check_limit arguments", 3,
      "31.4.3"));
}

TEST(TimingCheckCommandParsing, PeriodControlledReferenceNoDataEvent) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk, 50);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
  EXPECT_TRUE(tc->data_terminal.name.empty());
  ASSERT_EQ(tc->limits.size(), 1u);
}

TEST(TimingCheckCommandParsing, WidthThresholdNoDataEvent) {
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
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->ref_terminal.name, "clk");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
  EXPECT_TRUE(tc->data_terminal.name.empty());
  ASSERT_EQ(tc->limits.size(), 2u);
}

TEST(TimingCheckCommandParsing, RecremTakesConditionsAndDelayedSignals) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge rst, posedge clk, 10, 5, n, tsc, tcc, dr, dd);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kRecrem);
  EXPECT_EQ(tc->notifier, "n");
  EXPECT_NE(tc->timestamp_cond, nullptr);
  EXPECT_NE(tc->timecheck_cond, nullptr);
  EXPECT_EQ(tc->delayed_ref, "dr");
  EXPECT_EQ(tc->delayed_data, "dd");
}

TEST(TimingCheckCommandParsing, ChecksEndingAtTheNotifierTakeNothingPastIt) {
  const char* const kChecks[] = {
      "$setup(d, posedge clk, 10, n, tsc)",
      "$hold(posedge clk, d, 10, n, tsc, tcc, dr, dd)",
      "$recovery(posedge clk, d, 10, n, 1)",
      "$removal(posedge clk, d, 10, n, 1)",
      "$skew(posedge clk, d, 10, n, 1)",
      "$period(posedge clk, 10, n, 1)",
      "$width(posedge clk, 10, 0, n, 1)",
      "$nochange(posedge clk, d, 0, 0, n, 1)",
  };
  for (const char* check : kChecks) {
    auto r = Parse(std::string("module m;\nspecify\n  ") + check +
                   ";\nendspecify\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ','", 3, "31.2"))
        << check;
  }
}

TEST(TimingCheckCommandParsing,
     ChecksEndingAtTheNotifierTakeNothingPastItsSlot) {
  const char* const kChecks[] = {
      "$setup(d, posedge clk, 10, , tsc)",
      "$hold(posedge clk, d, 10, , tsc)",
      "$recovery(posedge clk, d, 10, , 1)",
      "$removal(posedge clk, d, 10, , 1)",
      "$skew(posedge clk, d, 10, , 1)",
      "$period(posedge clk, 10, , 1)",
      "$width(posedge clk, 10, 0, , 1)",
      "$nochange(posedge clk, d, 0, 0, , 1)",
  };
  for (const char* check : kChecks) {
    auto r = Parse(std::string("module m;\nspecify\n  ") + check +
                   ";\nendspecify\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ','", 3, "31.2"))
        << check;
  }
}

TEST(TimingCheckCommandParsing, ErrorMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10;\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 3, "31.2"));
}

TEST(TimingCheckCommandParsing, ErrorMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10)\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endspecify'", 4, "31.2"));
}

}  // namespace
