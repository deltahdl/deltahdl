#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

constexpr const char* kRangeAnd = "(te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5)";
constexpr const char* kFixedAnd = "(te1 ##2 te2) and (te3 ##2 te4 ##2 te5)";

std::string RangeDrive() {
  return DriveTicks(
      {{1, 2, 8}, {9, 10, 11, 12, 13}, {2, 3, 8}, {4, 10}, {6, 12}});
}

std::string FixedDrive() {
  return DriveTicks({{1, 2, 8}, {10, 12, 13}, {2, 3, 8}, {4, 10}, {6, 12}});
}

TEST(SequenceAndMatches, DISABLED_EachPairOfOperandMatchesIsAMatch) {
  std::string items = "  sequence s_and; ";
  items += kRangeAnd;
  items += "; endsequence\n  c1: cover sequence (@(posedge clk) ";
  items += kRangeAnd;
  items += ");\n  c2: cover sequence (@(posedge clk) s_and);\n";
  std::string src = SequenceCoverSource(items, RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 5u);
}

TEST(SequenceAndMatches, ARangeOperandAloneCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) te1 ##[1:5] te2);\n", RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
}

TEST(SequenceAndMatches, DISABLED_SwappedOperandsPairEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " (te3 ##2 te4 ##2 te5) and (te1 ##[1:5] te2));\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
}

TEST(SequenceAndMatches, DISABLED_ABooleanOperandPairsWithEveryRangeMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) (te1 ##[1:5] te2) and te1)"
      " at = $time;\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
  EXPECT_EQ(VarValue(f, "at"), 125u);
}

TEST(SequenceAndMatches, DISABLED_TwoRangeOperandsPairEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " (te1 ##[1:2] te2) and (te3 ##[1:2] te2));\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 4u);
}

TEST(SequenceAndMatches, DISABLED_EachMatchContinuesTheChainAfterIt) {
  std::string items = "  sequence s_and; ";
  items += kRangeAnd;
  items += "; endsequence\n  c1: cover sequence (@(posedge clk) (";
  items += kRangeAnd;
  items += ") ##1 te2);\n  c2: cover sequence (@(posedge clk) te3 ##0 (";
  items += kRangeAnd;
  items +=
      ") ##1 te2);\n"
      "  c3: cover sequence (@(posedge clk) te3 ##0 s_and ##1 te2);\n";
  std::string src = SequenceCoverSource(items, RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 4u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 4u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 4u);
}

TEST(SequenceAndMatches, ASingleMatchContinuesTheChainAfterIt) {
  std::string items = "  sequence s_and; ";
  items += kFixedAnd;
  items += "; endsequence\n  c1: cover sequence (@(posedge clk) (";
  items += kFixedAnd;
  items += ") ##1 te2) at = $time;\n";
  items += "  c2: cover sequence (@(posedge clk) te3 ##0 (";
  items += kFixedAnd;
  items +=
      ") ##1 te2);\n"
      "  c3: cover sequence (@(posedge clk) te3 ##0 s_and ##1 te2);\n"
      "  c4: cover sequence (@(posedge clk) te1 ##0 s_and ##1 te1);\n";
  std::string src = SequenceCoverSource(items, FixedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 125u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 0u);
}

TEST(SequenceAndMatches, AnOperandOpeningWithADelayStartsAtTheAttempt) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) te3 and ##1 te4) at = $time;\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 35u);
}

std::string OutsideSequences() {
  return "package pk;\n"
         "  sequence s_and(a, b, c, d, e);"
         " (a ##[1:5] b) and (c ##2 d ##2 e); endsequence\n"
         "endpackage\n"
         "sequence u_and(a, b, c, d, e);"
         " (a ##[1:5] b) and (c ##2 d ##2 e); endsequence\n";
}

TEST(SequenceAndMatches, APackageSequenceMatchesOnceAnAttempt) {
  std::string src = SequenceCoverSource(
      "  c1: cover property (@(posedge clk) pk::s_and(te1, te2, te3, te4,"
      " te5));\n",
      RangeDrive(), OutsideSequences());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(SequenceAndMatches,
     DISABLED_ACompilationUnitSequenceMatchesOnceAnAttempt) {
  std::string src = SequenceCoverSource(
      "  c2: cover property (@(posedge clk) u_and(te1, te2, te3, te4,"
      " te5));\n",
      RangeDrive(), OutsideSequences());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

TEST(SequenceAndMatches, DISABLED_ASequenceOutsideAModulePairsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) pk::s_and(te1, te2, te3, te4,"
      " te5));\n"
      "  c2: cover sequence (@(posedge clk) u_and(te1, te2, te3, te4,"
      " te5));\n",
      RangeDrive(), OutsideSequences());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 5u);
}

std::string DesignElementsSource(const std::string& directive) {
  std::string statement = directive + "(@(posedge clk) ";
  statement += kRangeAnd;
  statement += ");\n";
  return DesignElementCoverSource(statement, RangeDrive());
}

TEST(SequenceAndMatches, EveryDesignElementMatchesOnceAnAttempt) {
  std::string src = DesignElementsSource("cover property ");
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 1u);
}

TEST(SequenceAndMatches, DISABLED_EveryDesignElementPairsEveryMatch) {
  std::string src = DesignElementsSource("cover sequence ");
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 5u);
}

std::string InstanceOperands() {
  return "  sequence sa(x, y); x ##[1:5] y; endsequence\n"
         "  sequence sb(x, y, z); x ##2 y ##2 z; endsequence\n"
         "  sequence sf(sequence q); q and (te3 ##2 te4 ##2 te5);"
         " endsequence\n"
         "  sequence sm; int v; (te1 ##[1:5] te2, v = 1) and"
         " (te3 ##2 te4 ##2 te5); endsequence\n";
}

TEST(SequenceAndMatches, AProceduralAssertionOfInstancesMatchesOnce) {
  std::string src =
      SequenceCoverSource(InstanceOperands() +
                              "  always @(posedge clk) begin\n"
                              "    c1: cover property (sa(te1, te2) and"
                              " sb(te3, te4, te5));\n"
                              "  end\n",
                          RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(SequenceAndMatches, EveryKindOfOperandMatchesOnceAnAttempt) {
  std::string src = SequenceCoverSource(
      InstanceOperands() +
          "  c1: cover property (@(posedge clk) sa(te1, te2) and"
          " sb(te3, te4, te5));\n"
          "  c2: cover property (@(posedge clk) sf(te1 ##[1:5] te2));\n"
          "  c3: cover property (@(posedge clk) sm);\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
}

TEST(SequenceAndMatches, DISABLED_EveryKindOfOperandPairsEveryMatch) {
  std::string src = SequenceCoverSource(
      InstanceOperands() +
          "  c1: cover sequence (@(posedge clk) sa(te1, te2) and"
          " sb(te3, te4, te5));\n"
          "  c2: cover sequence (@(posedge clk) sf(te1 ##[1:5] te2));\n"
          "  c3: cover sequence (@(posedge clk) sm);\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 5u);
}

TEST(SequenceAndMatches, DISABLED_AGroupOfTwoInstancesIsEvaluated) {
  std::string src = SequenceCoverSource(
      InstanceOperands() +
          "  c1: cover sequence (@(posedge clk) (sa(te1, te2) and"
          " sb(te3, te4, te5)));\n",
      FixedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(SequenceAndImplication, AnAntecedentAttemptFailsOnce) {
  std::string items;
  for (const char* directive : {"assert", "assume"}) {
    for (const char* arrow : {"|->", "|=>"}) {
      items += "  ";
      items += directive;
      items += " property (@(posedge clk) (";
      items += kFixedAnd;
      items += ") ";
      items += arrow;
      items += " 1'b0) else fails++;\n";
    }
  }
  std::string src = SequenceCoverSource(items, FixedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 4u);
}

TEST(SequenceAndImplication, AConsequentNeedsBothOperands) {
  std::string items;
  for (const char* directive : {"assert", "assume"}) {
    items += "  ";
    items += directive;
    items += " property (@(posedge clk) te1 && te3 |-> ";
    items += kFixedAnd;
    items += ") else fails++;\n  ";
    items += directive;
    items +=
        " property (@(posedge clk) te1 && te3 |=>"
        " (te3 ##1 te4) and (##1 te4 ##2 te5)) else fails++;\n";
  }
  std::string src = SequenceCoverSource(items, FixedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 4u);
}

TEST(SequenceAndImplication, ACoverOfAnImplicationSucceedsWhereBothMatch) {
  std::string items = "  c1: cover property (@(posedge clk) (";
  items += kFixedAnd;
  items += ") |-> te5);\n  c2: cover property (@(posedge clk) (";
  items += kFixedAnd;
  items += ") |=> te2);\n  c3: cover property (@(posedge clk) te1 && te3 |-> ";
  items += kFixedAnd;
  items +=
      ");\n"
      "  c4: cover property (@(posedge clk) te1 && te3 |=>"
      " (te3 ##1 te4) and (##1 te4 ##2 te5));\n";
  std::string src = SequenceCoverSource(items, FixedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 1u);
}

}  // namespace
