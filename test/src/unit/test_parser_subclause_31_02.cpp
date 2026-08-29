#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §31.2, Syntax 31-1: system_timing_check enumerates twelve alternatives, one
// per timing-check keyword. This observes the top-level alternation directly --
// every one of the twelve, placed in a specify block, is dispatched to its own
// TimingCheckKind. Argument shapes are the minimal valid forms for each check
// (the detailed argument rules belong to the descendant subclauses); this test
// only pins the kind the §31.2 production selects.
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

// §31.2, Syntax 31-1: a system_timing_check opens with its own keyword, and
// TimingCheckDecl::loc (src/parser/ast_specify.h) is where the parser records
// the position of that keyword. A §31 violation is reported at that position,
// so a check whose position went unrecorded sends the reader to line 0 with
// nothing to open. The $setup below stands on line 4 of the source and starts
// at column 6. Neither number can be right by accident: a default-constructed
// SourceLoc (src/common/source_loc.h) carries line 0 and column 0, line 1 is
// the module header rather than the check, and column 1 is what an off-by-one
// or a position taken from the start of the line would give.
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
  // Five spaces precede the keyword on that line, so it starts at column 6.
  EXPECT_EQ(tc->loc.column, 6u);
}

// §31.2, Syntax 31-1: every system_timing_check a specify block holds records
// its own keyword's position. The $setup and the $hold below stand on lines 4
// and 5, so a position copied from the enclosing specify block or left over
// from whatever was parsed last would give the two declarations one line.
// Neither line is 1, which is what a default-constructed SourceLoc
// (src/common/source_loc.h) and the module header would give. Reaching the
// second check means walking ModuleItem::specify_items, because
// GetSoleTimingCheck in lib/cpp/test_helpers/helpers_parser_verify.h returns
// the first timing check of a block.
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
