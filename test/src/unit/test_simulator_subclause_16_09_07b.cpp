#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

constexpr const char* kTwoTickOr = "(te1 ##1 te2) or (te1 ##2 te3)";

std::string SameTickDrive() { return DriveTicks({{2}, {3}, {3}}); }

std::string TwoTickDrive() { return DriveTicks({{2}, {3}, {4}}); }

TEST(SequenceOrMatches, DISABLED_TwoMatchesEndingAtOneTickAreTwoMatches) {
  std::string src = SequenceCoverSource(
      "  sequence s; @(posedge clk) (te1 ##1 te2) or (te1 ##1 te3);"
      " endsequence\n"
      "  c1: cover sequence (s);\n"
      "  c2: cover sequence (@(posedge clk)"
      " ((te1 ##1 te2) or (te1 ##1 te2 ##0 1)));\n"
      "  c3: cover sequence (@(posedge clk)"
      " ((te1 ##1 te2) or (te1 ##1 te3)));\n",
      SameTickDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
}

TEST(SequenceOrMatches, DISABLED_AnAttachedCallRunsOncePerMatch) {
  std::string src = SequenceCoverSource(
      "  int n1 = 0, n2 = 0;\n"
      "  function void inc1(); n1++; endfunction\n"
      "  function void inc2(); n2++; endfunction\n"
      "  cover sequence (@(posedge clk)"
      " ((te1 ##1 te2) or (te1 ##1 te3), inc1()));\n"
      "  cover property (@(posedge clk)"
      " ((te1 ##1 te2) or (te1 ##1 te3), inc2()));\n",
      SameTickDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "n1"), 2u);
  EXPECT_EQ(VarValue(f, "n2"), 2u);
}

TEST(SequenceOrMatches, DISABLED_FigureElevenCountsSixMatches) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " (te1 ##[1:5] te2) or (te3 ##2 te4 ##2 te5)) at = $time;\n"
      "  c2: cover sequence (@(posedge clk)"
      " ((te1 ##[1:5] te2) or (te3 ##2 te4 ##2 te5)));\n",
      DriveTicks({{1, 2, 8}, {9, 10, 11, 12, 13}, {8}, {10}, {12}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 6u);
  EXPECT_EQ(VarValue(f, "at"), 125u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 6u);
}

TEST(SequenceOrMatches, DISABLED_AWholeOrOfACoverSequenceCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  default clocking @(posedge clk); endclocking\n"
      "  c1: cover sequence (@(posedge clk) (te1 ##1 te2) or"
      " (te1 ##2 te3));\n"
      "  c2: cover sequence (@(posedge clk) te1 ##1 te2 or te1 ##2 te3);\n"
      "  c3: cover sequence (@(posedge clk) te1 ##1 te2 ##1 te3 or te1);\n"
      "  c4: cover sequence ((te1 ##1 te2) or (te1 ##2 te3));\n",
      TwoTickDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 2u);
}

TEST(SequenceOrMatches, AGroupedOrCountsEveryMatchEndingAtItsOwnTick) {
  std::string items = "  sequence s; ";
  items += kTwoTickOr;
  items += "; endsequence\n  c1: cover sequence (@(posedge clk) (";
  items += kTwoTickOr;
  items += ")) at = $time;\n  c2: cover sequence (@(posedge clk) (";
  items += kTwoTickOr;
  items +=
      ") ##0 1);\n"
      "  c3: cover sequence (@(posedge clk) te1 ##1 (te2 or (1 ##1 te3)));\n"
      "  c4: cover sequence (@(posedge clk) s);\n";
  std::string src = SequenceCoverSource(items, TwoTickDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(VarValue(f, "at"), 35u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 2u);
}

std::string OutsideSequences() {
  return "package pk;\n"
         "  sequence s_or(a, b, c); (a ##1 b) or (a ##2 c); endsequence\n"
         "endpackage\n"
         "sequence u_or(a, b, c); (a ##1 b) or (a ##2 c); endsequence\n";
}

TEST(SequenceOrPlaces, APackageSequenceCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover property (@(posedge clk) pk::s_or(te1, te2, te3));\n"
      "  c2: cover sequence (@(posedge clk) pk::s_or(te1, te2, te3));\n",
      TwoTickDrive(), OutsideSequences());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
}

TEST(SequenceOrPlaces, DISABLED_ACompilationUnitSequenceCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover property (@(posedge clk) u_or(te1, te2, te3));\n"
      "  c2: cover sequence (@(posedge clk) u_or(te1, te2, te3));\n",
      TwoTickDrive(), OutsideSequences());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
}

TEST(SequenceOrPlaces, EveryDesignElementSucceedsOnceAnAttempt) {
  std::string statement = "cover property (@(posedge clk) ";
  statement += kTwoTickOr;
  statement += ");\n";
  std::string src = DesignElementCoverSource(statement, TwoTickDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 1u);
}

TEST(SequenceOrPlaces, EveryDesignElementCountsEveryMatch) {
  std::string statement = "cover sequence (@(posedge clk) (";
  statement += kTwoTickOr;
  statement += "));\n";
  std::string src = DesignElementCoverSource(statement, TwoTickDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 2u);
}

TEST(SequenceOrOperands, InstancesWithActualsAreOperands) {
  std::string src = SequenceCoverSource(
      "  sequence sa(x, y); x ##1 y; endsequence\n"
      "  sequence sb(x, y); x ##2 y; endsequence\n"
      "  sequence sn; sa(te1, te2) or sb(te1, te3); endsequence\n"
      "  always @(posedge clk) begin\n"
      "    c1: cover property (sa(te1, te2) or sb(te1, te3));\n"
      "  end\n"
      "  c2: cover sequence (@(posedge clk) (sa(te1, te2) or (te1 ##2 te3)));\n"
      "  c3: cover sequence (@(posedge clk) sn);\n",
      TwoTickDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
}

TEST(SequenceOrOperands, DISABLED_AGroupOfTwoInstancesIsEvaluated) {
  std::string src = SequenceCoverSource(
      "  sequence sa(x, y); x ##1 y; endsequence\n"
      "  sequence sb(x, y); x ##2 y; endsequence\n"
      "  c1: cover sequence (@(posedge clk) (sa(te1, te2) or sb(te1, te3)));\n",
      TwoTickDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
}

std::string ImplicationDrive() {
  return DriveTicks({{2, 6}, {3}, {4}, {3}, {4}});
}

TEST(SequenceOrImplication, EveryDirectiveTakesItOnEitherSide) {
  std::string items;
  for (const char* directive : {"assert", "assume"}) {
    std::string head = "  ";
    head += directive;
    head += " property (@(posedge clk) ";
    items += head + "(" + kTwoTickOr + ") |-> te4) else fails++;\n";
    items += head + "(" + kTwoTickOr + ") |=> te5) else fails++;\n";
    items += head + "te1 |-> (##1 te2) or (##1 te3)) else fails++;\n";
    items += head + "te1 |=> te2 or te3) else fails++;\n";
  }
  items += "  c1: cover property (@(posedge clk) (";
  items += kTwoTickOr;
  items +=
      ") |-> te4 || te5);\n"
      "  c2: cover property (@(posedge clk) te1 |-> (##1 te2) or"
      " (##1 te3));\n";
  std::string src = SequenceCoverSource(items, ImplicationDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 8u);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

}  // namespace
