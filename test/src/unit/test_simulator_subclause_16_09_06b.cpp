#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

constexpr const char* kRangeIntersect =
    "(te1 ##[1:5] te2) intersect (te3 ##2 te4 ##2 te5)";

std::string RangeDrive() {
  return DriveTicks(
      {{1, 2, 8}, {9, 10, 11, 12, 13}, {2, 3, 8}, {4, 10}, {6, 12}});
}

std::string EmptyDrive() { return DriveTicks({{1, 2, 4, 7, 8}, {2, 3, 4, 7}}); }

TEST(SequenceIntersectEmpty, EachOperandAloneAdmitsItsEmptyMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover property (@(posedge clk) te1 ##1 te2);\n"
      "  c2: cover property (@(posedge clk) te1 ##1 te2[*0] ##1 te2);\n"
      "  c3: cover property (@(posedge clk)"
      " te1 ##1 (te1 ##1 te1)[*0:1] ##1 te2);\n"
      "  c4: cover property (@(posedge clk)"
      " te1 ##1 (te2[*0:1] intersect te2[*0:1]) ##1 te2);\n",
      EmptyDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 2u);
}

TEST(SequenceIntersectEmpty, DISABLED_TwoEmptyMatchesPairIntoAnEmptyMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover property (@(posedge clk)"
      " te1 ##1 (te2[*0:1] intersect (te1 ##1 te1)[*0:1]) ##1 te2);\n"
      "  c2: cover property (@(posedge clk)"
      " te1 ##1 (te2[*0] intersect te1[*0]) ##1 te2);\n"
      "  c3: cover property (@(posedge clk)"
      " te1 ##1 (te2[*0:1] intersect te1[*0]) ##1 te2);\n"
      "  c4: cover property (@(posedge clk)"
      " te1 ##1 (te2[*0:2] intersect te1[*0:1]) ##1 te2);\n"
      "  c5: cover sequence (@(posedge clk)"
      " te1 ##1 (te2[*0:2] intersect te1[*0:1]) ##1 te2);\n",
      EmptyDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c5:"), 3u);
}

TEST(SequenceIntersectEmpty, DISABLED_AnEmptyPairStandsInAnImplication) {
  std::string src = SequenceCoverSource(
      "  c1: cover property (@(posedge clk)"
      " te1 |=> (te2[*0:1] intersect (te1 ##1 te1)[*0:1]) ##1 te2);\n"
      "  assert property (@(posedge clk)"
      " te1 |=> (te2[*0:1] intersect (te1 ##1 te1)[*0:1]) ##1 te2)"
      " else fails++;\n",
      EmptyDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(VarValue(f, "fails"), 3u);
}

TEST(SequenceIntersectEmpty, DISABLED_AnEmptyPairEndsADeclaredSequence) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(
          "te1 ##1 (te2[*0:1] intersect (te1 ##1 te1)[*0:1]) ##1 te2",
          EmptyDrive()),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(VarValue(f, "last"), 25u);
}

TEST(SequenceIntersectOperands, BooleanOperandsPairWhereTheyHoldAtOneTick) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) te1 intersect te2) at = $time;\n"
      "  c2: cover sequence (@(posedge clk) te1 intersect te3[*1:2]);\n"
      "  always @(posedge clk) begin\n"
      "    c3: cover sequence (te1 intersect (te2 ##1 te1));\n"
      "  end\n",
      DriveTicks({{1, 3, 8, 14}, {1, 3, 5, 8, 9, 14}, {1, 2, 8, 9}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 4u);
  EXPECT_EQ(VarValue(f, "at"), 135u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 0u);
}

TEST(SequenceIntersectMatches, OnlyTheEqualLengthPairOfFigureEightMatches) {
  std::string items = "  c1: cover sequence (@(posedge clk) ";
  items += kRangeIntersect;
  items += ") at = $time;\n";
  std::string src = SequenceCoverSource(items, RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 115u);
}

TEST(SequenceIntersectMatches, EachEqualLengthPairIsAMatch) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " (te1 ##[1:2] te2) intersect (te3 ##[1:2] te2));\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
}

TEST(SequenceIntersectMatches, DISABLED_TwoOperandMatchesOfOneLengthEachPair) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " (te1 ##[1:2] te2 ##[1:2] te2) intersect (te3 ##3 1'b1)) at = $time;\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(VarValue(f, "at"), 105u);
}

std::string OutsideSequences() {
  return "package pk;\n"
         "  sequence s_x(a, b, c, d, e);"
         " (a ##[1:5] b) intersect (c ##2 d ##2 e); endsequence\n"
         "endpackage\n"
         "sequence u_x(a, b, c, d, e);"
         " (a ##[1:5] b) intersect (c ##2 d ##2 e); endsequence\n";
}

TEST(SequenceIntersectPlaces, APackageSequenceMatchesOnce) {
  std::string src = SequenceCoverSource(
      "  c1: cover property (@(posedge clk) pk::s_x(te1, te2, te3, te4,"
      " te5));\n"
      "  c2: cover sequence (@(posedge clk) pk::s_x(te1, te2, te3, te4,"
      " te5));\n",
      RangeDrive(), OutsideSequences());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

TEST(SequenceIntersectPlaces, DISABLED_ACompilationUnitSequenceMatchesOnce) {
  std::string src = SequenceCoverSource(
      "  c1: cover property (@(posedge clk) u_x(te1, te2, te3, te4, te5));\n"
      "  c2: cover sequence (@(posedge clk) u_x(te1, te2, te3, te4, te5));\n",
      RangeDrive(), OutsideSequences());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

TEST(SequenceIntersectPlaces, EveryDesignElementAndGenerateBlockMatchesOnce) {
  std::string statement = "cover sequence (@(posedge clk) ";
  statement += kRangeIntersect;
  statement += ");\n";
  std::string src = DesignElementCoverSource(statement, RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 1u);
}

TEST(SequenceIntersectPlaces, AProceduralAssertionOfInstancesMatchesOnce) {
  std::string src = SequenceCoverSource(
      "  sequence sa(x, y); x ##[1:5] y; endsequence\n"
      "  sequence sb(x, y, z); x ##2 y ##2 z; endsequence\n"
      "  always @(posedge clk) begin\n"
      "    c1: cover property (sa(te1, te2) intersect sb(te3, te4, te5));\n"
      "  end\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(SequenceIntersectOperands, DISABLED_ASequenceFormalIsAnOperand) {
  std::string src = SequenceCoverSource(
      "  sequence sf(sequence q); q intersect (te3 ##2 te4 ##2 te5);"
      " endsequence\n"
      "  sequence su(q); q intersect (te3 ##2 te4 ##2 te5); endsequence\n"
      "  c1: cover property (@(posedge clk) sf(te1 ##[1:5] te2));\n"
      "  c2: cover property (@(posedge clk) su(te1 ##[1:5] te2));\n",
      RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

TEST(SequenceIntersectImplication, EveryDirectiveTakesItOnEitherSide) {
  std::string items;
  for (const char* directive : {"assert", "assume"}) {
    items += "  ";
    items += directive;
    items += " property (@(posedge clk) (";
    items += kRangeIntersect;
    items += ") |-> 1'b0) else fails++;\n  ";
    items += directive;
    items +=
        " property (@(posedge clk) te1 && te3 |=>"
        " (te2 ##[0:4] te2) intersect te2[*3]) else fails++;\n";
  }
  items += "  c1: cover property (@(posedge clk) (";
  items += kRangeIntersect;
  items +=
      ") |-> te5);\n"
      "  c2: cover property (@(posedge clk) te1 && te3 |=>"
      " (te2 ##[0:4] te2) intersect te2[*3]);\n";
  std::string src = SequenceCoverSource(items, RangeDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 4u);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

}  // namespace
