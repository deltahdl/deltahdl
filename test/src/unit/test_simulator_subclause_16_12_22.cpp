#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "helpers_property_places.h"

namespace {

std::string MatchSource(const std::string& items) {
  return "module m;\n"
         "  logic clk = 0, a = 0, b = 0;\n"
         "  sequence never; 1'b1 intersect (1'b1 ##1 1'b1); endsequence\n"
         "  always #5 clk = ~clk;\n"
         "  initial begin #10 a = 1; b = 1; #30 $finish; end\n" +
         items + "endmodule\n";
}

size_t HitsOfCover(const std::string& cover) {
  return CountThroughTheEnd(
             MatchSource("  " + cover + " $display(\"PASS\");\n"))
      .passes;
}

constexpr const char* kUngroupedOfEqualLength[] = {
    "(a ##1 b) intersect (a ##1 b) intersect (a ##1 b)",
    "(a ##1 b) and ((a ##1 b) intersect (a ##1 b))",
    "(a ##1 b) intersect (b throughout (a ##1 b))"};

TEST(NondegeneracyRun, AnUngroupedChainOfEqualLengthMatchesAtEachEnd) {
  for (const char* seq : kUngroupedOfEqualLength) {
    SCOPED_TRACE(seq);
    EXPECT_EQ(
        HitsOfCover(std::string("cover property (@(posedge clk) ") + seq + ")"),
        2u);
  }
}

TEST(NondegeneracyRun,
     DISABLED_ADoublyParenthesizedOrFirstMatchOperandMatchesAtEachEnd) {
  for (const char* seq : {"(a ##1 b) intersect first_match(a ##1 b)",
                          "(a ##1 b) intersect ((a ##1 b))", "((a ##1 b))"}) {
    SCOPED_TRACE(seq);
    EXPECT_EQ(
        HitsOfCover(std::string("cover property (@(posedge clk) ") + seq + ")"),
        2u);
  }
}

constexpr const char* kGroupsOfEqualLength[] = {
    "(a ##1 b) intersect ((a ##1 b) intersect (a ##1 b))",
    "((a ##1 b) intersect (a ##1 b)) intersect (a ##1 b)",
    "(a ##1 b) intersect ((a ##1 b) or (a ##1 b))",
    "(a ##1 b) intersect ((a ##1 b) and (a ##1 b))",
    "(a ##1 b) intersect ((a ##1 b) within (a ##1 b))",
    "(a ##1 b) within ((a ##1 b) intersect (a ##1 b))"};

TEST(NondegeneracyRun, DISABLED_AGroupOfEqualLengthMatchesAtEachEnd) {
  for (const char* seq : kGroupsOfEqualLength) {
    SCOPED_TRACE(seq);
    EXPECT_EQ(
        HitsOfCover(std::string("cover property (@(posedge clk) ") + seq + ")"),
        2u);
  }
}

constexpr const char* kUnmatchable[] = {"a[*0] ##0 b", "1 intersect (1 ##1 1)",
                                        "never"};

TEST(NondegeneracyRun, AProceduralCoverSequenceOverNoMatchCountsNone) {
  EXPECT_EQ(HitsOfCover("always @(posedge clk) cover sequence (a ##1 b)"), 2u);
  for (const char* seq : kUnmatchable) {
    SCOPED_TRACE(seq);
    EXPECT_EQ(
        HitsOfCover(std::string("always @(posedge clk) cover sequence (") +
                    seq + ")"),
        0u);
  }
}

TEST(NondegeneracyRun, DISABLED_ACoverSequenceOverNoMatchCountsNone) {
  for (const char* seq : kUnmatchable) {
    SCOPED_TRACE(seq);
    EXPECT_EQ(
        HitsOfCover(std::string("cover sequence (@(posedge clk) ") + seq + ")"),
        0u);
  }
}

}  // namespace
