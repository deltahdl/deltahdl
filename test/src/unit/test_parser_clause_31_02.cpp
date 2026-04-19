#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Exercises the specify-block dispatch: the overview grammar permits any mix
// of system_timing_check forms within a single specify block.
TEST(SystemTimingCheckParsing, MultipleTimingChecksInSpecifyBlock) {
  auto r = Parse(
      "module m(input d, clk, rst);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "    $hold(posedge clk, d, 3);\n"
      "    $recovery(posedge clk, rst, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kSetup);
  EXPECT_EQ(spec->specify_items[1]->timing_check.check_kind,
            TimingCheckKind::kHold);
  EXPECT_EQ(spec->specify_items[2]->timing_check.check_kind,
            TimingCheckKind::kRecovery);
}

// A timing-check name used outside a specify block must be diagnosed; the
// leading $ is historical, not a signal that they behave like system tasks.
TEST(SystemTimingCheckParsing, TimingCheckRejectedInAlwaysBlock) {
  auto r = Parse(
      "module m(input d, clk);\n"
      "  always @(posedge clk) $setup(d, posedge clk, 5);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SystemTimingCheckParsing, TimingCheckRejectedInInitialBlock) {
  auto r = Parse(
      "module m(input d, clk);\n"
      "  initial $hold(posedge clk, d, 3);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// Every one of the twelve timing-check names is banned from procedural code.
TEST(SystemTimingCheckParsing, EveryTimingCheckRejectedInProceduralCode) {
  const char* names[] = {"$setup",    "$hold",     "$setuphold", "$recovery",
                         "$removal",  "$recrem",   "$skew",      "$timeskew",
                         "$fullskew", "$period",   "$width",     "$nochange"};
  for (const char* n : names) {
    std::string src = "module m; initial ";
    src += n;
    src += "(a, b, 1); endmodule\n";
    auto r = Parse(src);
    EXPECT_TRUE(r.has_errors) << "expected rejection of " << n;
  }
}

// Only timing checks may appear at a specify-block item position; any other
// $identifier is a system task and shall not occur there.
TEST(SystemTimingCheckParsing, SystemTaskRejectedInSpecifyBlock) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    $display(\"hi\");\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SystemTimingCheckParsing, FinishRejectedInSpecifyBlock) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    $finish;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
