#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

std::string RangeDrive() { return DriveTicks({{1, 2, 3}, {1}, {2, 3, 4}}); }

TEST(ThroughoutMatches, EachMatchInsideTheConditionIsAMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " te1 throughout (te2 ##[1:3] te3)) at = $time;\n"
      "  c2: cover sequence (@(posedge clk)"
      " (te1)[*0:$] intersect (te2 ##[1:3] te3));\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(VarValue(f, "at"), 25u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
}

TEST(ThroughoutMatches, EachAttemptHasItsOwnInterval) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " te1 throughout (te2 ##2 te3)) at = $time;\n",
      DriveTicks({{2, 3, 4}, {1, 2}, {3, 4}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 35u);
}

TEST(ThroughoutMatches, AOneTickSequenceMatchesWhereBothHold) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) te1 throughout te2) at = $time;\n",
      DriveTicks({{2, 3}, {3, 4}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 25u);
}

TEST(ThroughoutMatches, DISABLED_AnEmptyMatchOfTheSequenceIsAMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " te4 ##1 (te1 throughout te2[*0:1]) ##1 te3) at = $time;\n",
      DriveTicks({{}, {2}, {2}, {1}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 15u);
}

TEST(ThroughoutOperands, EveryKindOfConditionGuardsTheSequence) {
  std::string src = SequenceCoverSource(
      "  function bit f(bit y); return y; endfunction\n"
      "  sequence sw; @(posedge clk) te1; endsequence\n"
      "  sequence g(w); w throughout (te2 ##[1:3] te3); endsequence\n"
      "  c1: cover sequence (@(posedge clk)"
      " te1 dist {1 := 1} throughout (te2 ##[1:3] te3));\n"
      "  c2: cover sequence (@(posedge clk)"
      " f(te1) throughout (te2 ##[1:3] te3));\n"
      "  c3: cover sequence (@(posedge clk)"
      " sw.triggered throughout (te2 ##[1:3] te3));\n"
      "  c4: cover sequence (@(posedge clk) g(te1));\n"
      "  c5: cover sequence (@(posedge clk)"
      " (te1 && !te4) throughout (te2 ##[1:3] te3));\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c5:"), 2u);
}

TEST(ThroughoutOperands, DISABLED_AnUnclockedSequencesTriggeredGuardsIt) {
  std::string src = SequenceCoverSource(
      "  sequence sw; te1; endsequence\n"
      "  c1: cover sequence (@(posedge clk)"
      " sw.triggered throughout (te2 ##[1:3] te3));\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
}

TEST(ThroughoutOperands, EveryKindOfSequenceIsGuarded) {
  std::string src = SequenceCoverSource(
      "  sequence sm(x, y); x ##[1:3] y; endsequence\n"
      "  c1: cover sequence (@(posedge clk) te1 throughout sm(te2, te3));\n"
      "  c2: cover sequence (@(posedge clk)"
      " te1 throughout pk::sp(te2, te3));\n",
      RangeDrive(),
      "package pk;\n"
      "  sequence sp(x, y); x ##[1:3] y; endsequence\n"
      "endpackage\n");
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
}

TEST(ThroughoutOperands, DISABLED_ASequenceWithoutArgumentsIsGuarded) {
  std::string src = SequenceCoverSource(
      "  sequence sn; te2 ##[1:3] te3; endsequence\n"
      "  c1: cover sequence (@(posedge clk) te1 throughout sn);\n"
      "  c2: cover property (@(posedge clk) te1 throughout sn |-> te1);\n",
      DriveTicks({{1, 2, 3}, {1}, {2, 3, 4}, {}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

TEST(ThroughoutOperands, ASequenceFormalIsGuarded) {
  std::string src = SequenceCoverSource(
      "  sequence sq(sequence q); te1 throughout q; endsequence\n"
      "  c1: cover sequence (@(posedge clk) sq(te2 ##[1:3] te3));\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
}

std::string OutsideThroughout() {
  return "package pk;\n"
         "  sequence st(a, b, c); a throughout (b ##[1:3] c); endsequence\n"
         "endpackage\n"
         "sequence ut(a, b, c); a throughout (b ##[1:3] c); endsequence\n";
}

TEST(ThroughoutPlaces, APackageSequenceCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) pk::st(te1, te2, te3));\n",
      RangeDrive(), OutsideThroughout());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
}

TEST(ThroughoutPlaces, DISABLED_ACompilationUnitSequenceCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) ut(te1, te2, te3));\n",
      RangeDrive(), OutsideThroughout());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
}

TEST(ThroughoutPlaces, EveryDesignElementCountsEveryMatch) {
  std::string src = DesignElementCoverSource(
      "cover sequence (@(posedge clk) te1 throughout (te2 ##[1:3] te3));\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 2u);
}

TEST(ThroughoutPlaces, AProceduralAssertionCountsEveryMatch) {
  std::string src = SequenceCoverSource(
      "  always @(posedge clk) begin\n"
      "    c1: cover sequence (te1 throughout (te2 ##[1:3] te3));\n"
      "    c2: cover property (te1 throughout (te2 ##[1:3] te3));\n"
      "  end\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

TEST(ThroughoutImplication, EveryDirectiveTakesItOnEitherSide) {
  std::string items;
  for (const char* directive : {"assert", "assume"}) {
    std::string head = "  ";
    head += directive;
    head += " property (@(posedge clk) ";
    items += head + "(te1 throughout (te2 ##[1:3] te3)) |-> te4)" +
             " else fails++;\n";
    items +=
        head + "te2 |=> (te1 throughout (##[0:2] te3)))" + " else fails++;\n";
  }
  items +=
      "  c1: cover property (@(posedge clk)"
      " (te1 throughout (te2 ##[1:3] te3)) |-> te4);\n"
      "  c2: cover property (@(posedge clk)"
      " te2 |=> (te1 throughout (##[0:2] te3)));\n";
  std::string src = SequenceCoverSource(
      items, DriveTicks({{1, 2, 3}, {1, 5}, {2, 3, 4}, {2}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 4u);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 0u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

}  // namespace
