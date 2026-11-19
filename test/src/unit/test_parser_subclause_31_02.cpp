#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
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

constexpr std::string_view kWellFormedTimingChecks[] = {
    "$setup(d, posedge clk, 2);",
    "$hold(posedge clk, d, 2);",
    "$setuphold(posedge clk, d, 1, 2);",
    "$recovery(posedge rst, clk, 2);",
    "$removal(posedge rst, clk, 2);",
    "$recrem(posedge rst, clk, 1, 2);",
    "$skew(posedge clk, d, 2);",
    "$timeskew(posedge clk, d, 2);",
    "$fullskew(posedge clk, negedge d, 1, 2);",
    "$period(posedge clk, 10);",
    "$width(posedge clk, 5);",
    "$nochange(posedge clk, d, 0, 0);",
    "$setup(d &&& en, edge [01, 10] clk, 2);",
    "$width(negedge clk &&& (en == 1'b1), 5);"};

size_t ErrorCount(const ParseResult& r) {
  size_t count = 0;
  for (const Diagnostic& d : r.diags) {
    if (d.severity == DiagSeverity::kError) ++count;
  }
  return count;
}

void ExpectOneProceduralRejection(std::string_view before,
                                  std::string_view after) {
  for (std::string_view check : kWellFormedTimingChecks) {
    std::string src(before);
    src += check;
    src += after;
    auto r = Parse(src);
    EXPECT_EQ(ErrorCount(r), 1u) << src;
    EXPECT_TRUE(ReportedError(
        r.diags, "timing check cannot appear in procedural code", 2, "31.2"))
        << src;
  }
}

constexpr std::string_view kModuleHead =
    "module m(input clk, input d, input rst, input en);\n  ";

TEST(SystemTimingCheckParsing, DISABLED_InInitialProcedureDrawsOneError) {
  ExpectOneProceduralRejection(std::string(kModuleHead) + "initial ",
                               "\nendmodule\n");
}

TEST(SystemTimingCheckParsing, DISABLED_InFinalProcedureDrawsOneError) {
  ExpectOneProceduralRejection(std::string(kModuleHead) + "final ",
                               "\nendmodule\n");
}

TEST(SystemTimingCheckParsing, DISABLED_InAlwaysProcedureDrawsOneError) {
  ExpectOneProceduralRejection(std::string(kModuleHead) + "always ",
                               "\nendmodule\n");
}

TEST(SystemTimingCheckParsing, DISABLED_InAlwaysCombProcedureDrawsOneError) {
  ExpectOneProceduralRejection(std::string(kModuleHead) + "always_comb ",
                               "\nendmodule\n");
}

TEST(SystemTimingCheckParsing, DISABLED_InAlwaysFfProcedureDrawsOneError) {
  ExpectOneProceduralRejection(
      std::string(kModuleHead) + "always_ff @(posedge clk) ", "\nendmodule\n");
}

TEST(SystemTimingCheckParsing, DISABLED_InAlwaysLatchProcedureDrawsOneError) {
  ExpectOneProceduralRejection(std::string(kModuleHead) + "always_latch ",
                               "\nendmodule\n");
}

TEST(SystemTimingCheckParsing, DISABLED_InNestedStatementsDrawsOneError) {
  ExpectOneProceduralRejection(std::string(kModuleHead) + "initial begin #1 ",
                               " end\nendmodule\n");
  ExpectOneProceduralRejection(std::string(kModuleHead) + "initial if (en) ",
                               "\nendmodule\n");
  ExpectOneProceduralRejection(std::string(kModuleHead) + "initial fork ",
                               " join\nendmodule\n");
}

TEST(SystemTimingCheckParsing, DISABLED_InTaskAndFunctionDrawsOneError) {
  ExpectOneProceduralRejection(std::string(kModuleHead) + "task t; ",
                               " endtask\nendmodule\n");
  ExpectOneProceduralRejection(std::string(kModuleHead) + "function void f; ",
                               " endfunction\nendmodule\n");
}

TEST(SystemTimingCheckParsing, DISABLED_InOtherDesignElementsDrawsOneError) {
  ExpectOneProceduralRejection(
      "interface i(input clk, input d, input rst, input en);\n  initial ",
      "\nendinterface\n");
  ExpectOneProceduralRejection(
      "program p(input clk, input d, input rst, input en);\n  initial ",
      "\nendprogram\n");
  ExpectOneProceduralRejection("class c;\n  task t; ", " endtask\nendclass\n");
  ExpectOneProceduralRejection("package k;\n  function void f; ",
                               " endfunction\nendpackage\n");
}

TEST(SystemTimingCheckParsing, EveryWellFormedCheckInSpecifyBlockIsAccepted) {
  for (std::string_view check : kWellFormedTimingChecks) {
    std::string src(kModuleHead);
    src += "specify\n    ";
    src += check;
    src += "\n  endspecify\nendmodule\n";
    auto r = Parse(src);
    EXPECT_EQ(ErrorCount(r), 0u) << src;
  }
}

}  // namespace
