#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Design(const std::string& declaration, const std::string& spec) {
  return "module t;\n  logic clk = 0;\n"
         "  initial repeat (20) #5 clk = ~clk;\n"
         "  bit a = 0, b = 0, c = 0, d = 1;\n  int tick = 0;\n"
         "  always @(negedge clk) begin\n    tick = tick + 1;\n"
         "    a = (tick == 1);\n    c = (tick == 2);\n  end\n"
         "  sequence inner_empty; int w = 2; b[*0]; endsequence\n"
         "  sequence inner_full; int w = 2; c; endsequence\n" +
         declaration + "  cover property (@(posedge clk) " + spec +
         ") $display(\"match %0d\", tick);\n" +
         "  initial #98 $display(\"done\");\nendmodule\n";
}

void ExpectMatch(const std::string& src, bool matched, int tick) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  std::string line = "match " + std::to_string(tick) + "\n";
  EXPECT_NE(out.find("done\n"), std::string::npos) << src << out;
  EXPECT_EQ(out.find(line) != std::string::npos, matched) << src << out;
}

void ExpectEmptyMatch(const std::string& rest, bool matched) {
  std::string sequence = "  sequence s; int v = 1; " + rest + "; endsequence\n";
  ExpectMatch(Design(sequence, "a ##1 s ##1 c"), matched, 2);
}

void ExpectLocalReadAfter(const std::string& rest) {
  ExpectMatch(Design("  sequence s; int v = tick; (" + rest +
                         ") ##1 (a && v == tick); endsequence\n",
                     "s"),
              true, 1);
  ExpectMatch(Design("  sequence s; int v = tick; (" + rest +
                         ") ##1 (a && v != tick); endsequence\n",
                     "s"),
              false, 1);
}

void ExpectKept(const std::string& rest) { ExpectEmptyMatch(rest, true); }

void ExpectNone(const std::string& rest) { ExpectEmptyMatch(rest, false); }

TEST(InitializedLocalEmptyMatch, ABooleanHasNone) {
  ExpectNone("b");
  ExpectNone("d");
}

TEST(InitializedLocalEmptyMatch, AnInnerDeclarationFollowsItsRest) {
  ExpectKept("inner_empty");
  ExpectNone("inner_full");
}

TEST(InitializedLocalEmptyMatch, AnAssignmentTickHasNone) {
  ExpectNone("(1, v = 2)");
}

TEST(InitializedLocalEmptyMatch, ParenthesesFollowTheSequenceInside) {
  ExpectKept("(b[*0])");
  ExpectNone("(c)");
}

TEST(InitializedLocalEmptyMatch, AConcatenationNeedsBothOperandsEmpty) {
  ExpectKept("b[*0] ##1 c[*0]");
  ExpectNone("b[*0] ##1 c");
  ExpectNone("c ##1 b[*0]");
}

TEST(InitializedLocalEmptyMatch, DISABLED_AFusionHasNone) {
  ExpectNone("c[*0:1] ##0 c[*0:1]");
}

TEST(InitializedLocalEmptyMatch, AFusionOfNonemptyOperandsHasNone) {
  ExpectNone("c ##0 d");
}

TEST(InitializedLocalEmptyMatch, DISABLED_AnOrNeedsOneOperandEmpty) {
  ExpectKept("b[*0] or c");
  ExpectKept("c or b[*0]");
}

TEST(InitializedLocalEmptyMatch, AnOrOfNonemptyOperandsHasNone) {
  ExpectNone("b or c");
}

TEST(InitializedLocalEmptyMatch,
     DISABLED_AnIntersectKeepsItWhenBothOperandsAreEmpty) {
  ExpectKept("b[*0] intersect c[*0]");
}

TEST(InitializedLocalEmptyMatch, AnIntersectWithANonemptyOperandHasNone) {
  ExpectNone("b[*0:1] intersect c");
  ExpectNone("c intersect b[*0:1]");
}

TEST(InitializedLocalEmptyMatch, AFirstMatchFollowsItsOperand) {
  ExpectKept("first_match(b[*0])");
  ExpectNone("first_match(c)");
}

TEST(InitializedLocalEmptyMatch, AZeroRepetitionKeepsIt) {
  ExpectKept("c[*0]");
  ExpectKept("b[*0]");
}

TEST(InitializedLocalEmptyMatch,
     DISABLED_AnUnboundedRepetitionOfAnEmptyOneKeepsIt) {
  ExpectKept("(b[*0])[*1:$]");
}

TEST(InitializedLocalEmptyMatch, AnUnboundedRepetitionOfANonemptyOneHasNone) {
  ExpectNone("c[*1:$]");
}

TEST(InitializedLocalEmptyMatch, AClockFollowsItsSequence) {
  ExpectKept("@(posedge clk) b[*0]");
  ExpectNone("@(posedge clk) c");
}

TEST(InitializedLocalAfterAnEmptyMatch, ItHoldsItsValueAfterZeroRepetitions) {
  ExpectLocalReadAfter("b[*0]");
  ExpectLocalReadAfter("b[*0] ##1 c[*0]");
}

TEST(InitializedLocalAfterAnEmptyMatch,
     DISABLED_ItHoldsItsValueAfterAFirstMatch) {
  ExpectLocalReadAfter("first_match(b[*0])");
}

TEST(InitializedLocalAfterAnEmptyMatch, DISABLED_ItHoldsItsValueAfterAnOr) {
  ExpectLocalReadAfter("b[*0] or c");
}

TEST(InitializedLocalAfterAnEmptyMatch,
     DISABLED_ItHoldsItsValueAfterAnIntersect) {
  ExpectLocalReadAfter("b[*0] intersect c[*0]");
}

TEST(InitializedLocalAfterAnEmptyMatch,
     DISABLED_ItHoldsItsValueAfterARepetition) {
  ExpectLocalReadAfter("(b[*0])[*1:$]");
}

TEST(InitializedLocalAfterAnEmptyMatch, ItHoldsItsValueAfterAClockedSequence) {
  ExpectLocalReadAfter("@(posedge clk) b[*0]");
}

}  // namespace
