#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

std::string Expansion(const std::string& inner, const std::string& outer) {
  return "(1[*0:$] ##1 " + inner + " ##1 1[*0:$]) intersect " + outer;
}

std::string PairCovers(const std::string& inner, const std::string& outer) {
  return "  c1: cover sequence (@(posedge clk) " + inner + " within " + outer +
         ") at = $time;\n"
         "  c2: cover sequence (@(posedge clk) " +
         Expansion(inner, outer) +
         ");\n"
         "  c3: cover property (@(posedge clk) " +
         inner + " within " + outer +
         ");\n"
         "  c4: cover property (@(posedge clk) " +
         Expansion(inner, outer) + ");\n";
}

std::string SpreadDrive() {
  return DriveTicks({{2, 3, 7}, {1, 2, 3, 4, 6, 7}, {3, 7}});
}

TEST(WithinExpansion, SeveralPlacementsMatchAsTheExpansionDoes) {
  std::string src = SequenceCoverSource(
      PairCovers("te1", "(te2 ##1 te2 ##1 te2)"), SpreadDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), CoverCount(f, src, "c2:"));
  EXPECT_EQ(VarValue(f, "at"), 35u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 2u);
}

TEST(WithinExpansion, AnInnerAdmittingAnEmptyMatchTakesEveryOuterMatch) {
  std::string src = SequenceCoverSource(
      PairCovers("te1[*0:1]", "(te2 ##1 te2)"), SpreadDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), CoverCount(f, src, "c2:"));
  EXPECT_EQ(VarValue(f, "at"), 65u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 4u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 4u);
}

TEST(WithinExpansion, AnEmptyOuterMatchGivesNoMatch) {
  std::string src =
      SequenceCoverSource(PairCovers("te1", "te2[*0:1]"), SpreadDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 3u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 3u);
  EXPECT_EQ(VarValue(f, "at"), 65u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 3u);
}

TEST(WithinExpansion, TwoBooleansMatchWhereBothHold) {
  std::string src =
      SequenceCoverSource(PairCovers("te1", "te3"), SpreadDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(VarValue(f, "at"), 65u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
}

std::string RangedDrive() { return DriveTicks({{3}, {1, 2, 3, 4, 5}}); }

TEST(WithinMatches, EachEndOfARangedOuterHoldingTheInnerIsAMatch) {
  std::string src = SequenceCoverSource(PairCovers("te1", "(te2 ##[1:3] te2)"),
                                        RangedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 7u);
  EXPECT_EQ(VarValue(f, "at"), 45u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 3u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 3u);
}

std::string OutsideWithin() {
  return "package pk;\n"
         "  sequence sw(a, b); a within (b ##[1:3] b); endsequence\n"
         "endpackage\n"
         "sequence uw(a, b); a within (b ##[1:3] b); endsequence\n";
}

TEST(WithinPlaces, APackageSequenceCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) pk::sw(te1, te2));\n"
      "  c2: cover property (@(posedge clk) pk::sw(te1, te2));\n",
      RangedDrive(), OutsideWithin());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 3u);
}

TEST(WithinPlaces, DISABLED_ACompilationUnitSequenceCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) uw(te1, te2));\n"
      "  c2: cover property (@(posedge clk) uw(te1, te2));\n",
      RangedDrive(), OutsideWithin());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 3u);
}

TEST(WithinPlaces, AGenerateBlockSequenceCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  if (1) begin : g\n"
      "    sequence sg; @(posedge clk) te1 within (te2 ##[1:3] te2);"
      " endsequence\n"
      "    c1: cover sequence (sg);\n"
      "    c2: cover property (sg);\n"
      "  end\n",
      RangedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 3u);
}

TEST(WithinPlaces, EveryDesignElementCountsEveryMatch) {
  std::string src = DesignElementCoverSource(
      "cover sequence (@(posedge clk) te1 within (te2 ##[1:3] te2));\n",
      RangedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 7u);
}

TEST(WithinPlaces, AProceduralAssertionOfInstancesCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  sequence si(x); x; endsequence\n"
      "  sequence so(x, y); x ##[1:3] y; endsequence\n"
      "  always @(posedge clk) begin\n"
      "    c1: cover sequence (si(te1) within so(te2, te2));\n"
      "    c2: cover property (si(te1) within so(te2, te2));\n"
      "  end\n",
      RangedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 3u);
}

TEST(WithinOperands, InstancesAndAGroupWithAnItemAreOperands) {
  std::string src = SequenceCoverSource(
      "  int items = 0;\n"
      "  function void item(); items++; endfunction\n"
      "  sequence si(x); x; endsequence\n"
      "  sequence so(x, y); x ##[1:3] y; endsequence\n"
      "  c1: cover sequence (@(posedge clk) si(te1) within so(te2, te2));\n"
      "  c2: cover sequence (@(posedge clk) (te1, item()) within"
      " (te2 ##[1:3] te2));\n",
      RangedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 7u);
  EXPECT_GT(VarValue(f, "items"), 0u);
}

TEST(WithinOperands, ASequenceFormalIsAnOperand) {
  std::string src = SequenceCoverSource(
      "  sequence sf(sequence q, sequence r); q within r; endsequence\n"
      "  c1: cover sequence (@(posedge clk) sf(te1, te2 ##[1:3] te2));\n"
      "  c2: cover property (@(posedge clk) sf(te1, te2 ##[1:3] te2));\n",
      RangedDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 7u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 3u);
}

TEST(WithinImplication, EveryDirectiveTakesItOnEitherSide) {
  std::string items;
  for (const char* directive : {"assert", "assume"}) {
    std::string head = "  ";
    head += directive;
    head += " property (@(posedge clk) ";
    items +=
        head + "(te1 within (te2 ##1 te2 ##1 te2)) |-> te3) else fails++;\n";
    items += head + "(te1 within (te2 ##1 te2 ##1 te2)) |=> te2)" +
             " else fails++;\n";
    items += head + "te4 |-> (te1 within (te2 ##1 te2))) else fails++;\n";
    items += head + "te4 |=> (te1 within te2)) else fails++;\n";
  }
  items +=
      "  c1: cover property (@(posedge clk)"
      " (te1 within (te2 ##1 te2 ##1 te2)) |-> te3);\n"
      "  c2: cover property (@(posedge clk)"
      " te4 |-> (te1 within (te2 ##1 te2)));\n"
      "  property pw; (te1 within (te2 ##1 te2 ##1 te2)) |=> te2;"
      " endproperty\n"
      "  c3: cover property (@(posedge clk) pw);\n"
      "  assert property (@(posedge clk) pw) else fails++;\n";
  std::string src = SequenceCoverSource(
      items, DriveTicks({{2, 3, 7}, {1, 2, 3, 4, 6, 7}, {3}, {1, 4}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 9u);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
}

}  // namespace
