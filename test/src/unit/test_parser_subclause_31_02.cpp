#include <gtest/gtest.h>

#include <cstddef>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(SystemTimingCheckParsing, EveryTimingCheckKindDispatched) {
  auto r = Parse(
      "module m(input d, clk, clk2, rst);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "    $hold(posedge clk, d, 3);\n"
      "    $setuphold(posedge clk, d, 5, 3);\n"
      "    $recovery(posedge rst, posedge clk, 4);\n"
      "    $removal(posedge rst, posedge clk, 4);\n"
      "    $recrem(posedge clk, rst, 5, 3);\n"
      "    $skew(posedge clk, negedge clk2, 3);\n"
      "    $timeskew(posedge clk, posedge clk2, 5);\n"
      "    $fullskew(posedge clk, negedge clk2, 4, 6);\n"
      "    $period(posedge clk, 50);\n"
      "    $width(posedge clk, 20, 1);\n"
      "    $nochange(posedge clk, d, 0, 0);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 12u);
  const TimingCheckKind kExpected[] = {
      TimingCheckKind::kSetup,     TimingCheckKind::kHold,
      TimingCheckKind::kSetuphold, TimingCheckKind::kRecovery,
      TimingCheckKind::kRemoval,   TimingCheckKind::kRecrem,
      TimingCheckKind::kSkew,      TimingCheckKind::kTimeskew,
      TimingCheckKind::kFullskew,  TimingCheckKind::kPeriod,
      TimingCheckKind::kWidth,     TimingCheckKind::kNochange};
  for (size_t i = 0; i < 12; ++i) {
    EXPECT_EQ(spec->specify_items[i]->timing_check.check_kind, kExpected[i])
        << "at specify item " << i;
  }
}

TEST(SystemTimingCheckParsing, EveryTimingCheckRejectedInProceduralCode) {
  const char* names[] = {"$setup",    "$hold",   "$setuphold", "$recovery",
                         "$removal",  "$recrem", "$skew",      "$timeskew",
                         "$fullskew", "$period", "$width",     "$nochange"};
  for (const char* n : names) {
    std::string src = "module m; initial ";
    src += n;
    src += "(a, b, 1); endmodule\n";
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(
        r.diags, "timing check cannot appear in procedural code", 1, "31.2"))
        << "expected rejection of " << n;
  }
}

TEST(SystemTimingCheckParsing, SystemTaskRejectedInSpecifyBlock) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    $display(\"hi\");\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "system task cannot appear in specify block", 3, "31.2"));
}

TEST(SystemTimingCheckParsing, TimingCheckRecordsItsKeywordPosition) {
  const std::string kSrc =
      "module m(input d, clk);\n"
      "  wire w;\n"
      "  specify\n"
      "     $setup(d, posedge clk, 5);\n"
      "  endspecify\n"
      "endmodule\n";
  auto r = Parse(kSrc);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->loc.line, LineHolding(kSrc, "$setup"));
  EXPECT_EQ(tc->loc.column, 6u);
}

TEST(SystemTimingCheckParsing, TwoTimingChecksRecordSeparateLines) {
  const std::string kSrc =
      "module m(input d, clk);\n"
      "  wire w;\n"
      "  specify\n"
      "     $setup(d, posedge clk, 5);\n"
      "       $hold(posedge clk, d, 3);\n"
      "  endspecify\n"
      "endmodule\n";
  auto r = Parse(kSrc);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 2u);
  EXPECT_EQ(spec->specify_items[0]->timing_check.loc.line,
            LineHolding(kSrc, "$setup"));
  EXPECT_EQ(spec->specify_items[1]->timing_check.loc.line,
            LineHolding(kSrc, "$hold"));
  EXPECT_NE(spec->specify_items[0]->timing_check.loc.line,
            spec->specify_items[1]->timing_check.loc.line);
}

}  // namespace
