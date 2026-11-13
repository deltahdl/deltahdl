#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

std::string EarliestDrive() { return DriveTicks({{1}, {3, 4}, {3}, {4}}); }

std::string TickCounter() {
  return "  int tick = 0;\n"
         "  always @(negedge clk) tick = tick + 1;\n";
}

TEST(FirstMatchInstance, DISABLED_AnInstanceWithActualsKeepsTheEarliestEnd) {
  std::string src = SequenceCoverSource(
      "  int n1 = 0, n2 = 0, n3 = 0, n4 = 0, n5 = 0, n6 = 0;\n"
      "  sequence ms(x, y); first_match(x ##[1:3] y); endsequence\n"
      "  sequence mt(x); first_match(x ##[1:3] te2); endsequence\n"
      "  sequence wrap; ms(te1, te2); endsequence\n"
      "  assert property (@(posedge clk) ms(te1, te2) |-> te3) else n1++;\n"
      "  assert property (@(posedge clk) ms(.x(te1), .y(te2)) |-> te3)"
      " else n2++;\n"
      "  assert property (@(posedge clk) ms(te1, te2) |=> te4) else n3++;\n"
      "  assert property (@(posedge clk) mt(te1) |-> te3) else n4++;\n"
      "  assert property (@(posedge clk) wrap |-> te3) else n5++;\n"
      "  assert property (@(posedge clk) pk::ps(te1, te2) |-> te3)"
      " else n6++;\n",
      EarliestDrive(),
      "package pk;\n"
      "  sequence ps(x, y); first_match(x ##[1:3] y); endsequence\n"
      "endpackage\n");
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "n1"), 0u);
  EXPECT_EQ(VarValue(f, "n2"), 0u);
  EXPECT_EQ(VarValue(f, "n3"), 0u);
  EXPECT_EQ(VarValue(f, "n4"), 0u);
  EXPECT_EQ(VarValue(f, "n5"), 0u);
  EXPECT_EQ(VarValue(f, "n6"), 0u);
}

TEST(FirstMatchInstance, DISABLED_AnInstancesMatchItemRunsAtTheFirstMatchOnly) {
  std::string src = SequenceCoverSource(
      "  int bumps = 0;\n"
      "  function void bump(); bumps++; endfunction\n"
      "  sequence mc(x, y); first_match(x ##[1:3] y, bump()); endsequence\n"
      "  assert property (@(posedge clk) mc(te1, te2) |-> te3)"
      " else fails++;\n",
      EarliestDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 0u);
  EXPECT_EQ(VarValue(f, "bumps"), 1u);
}

TEST(FirstMatchInstance, OtherFormsOfAnInstanceKeepTheEarliestEnd) {
  std::string src = SequenceCoverSource(
      "  int n1 = 0, n2 = 0, n3 = 0, n4 = 0;\n"
      "  sequence ms(x, y); first_match(x ##[1:3] y); endsequence\n"
      "  sequence mn; first_match(te1 ##[1:3] te2); endsequence\n"
      "  property mp(x, y); first_match(x ##[1:3] y) |-> te3; endproperty\n"
      "  assert property (@(posedge clk) mn |-> te3) else n1++;\n"
      "  assert property (@(posedge clk) mp(te1, te2)) else n2++;\n"
      "  assert property (@(posedge clk) first_match(ms(te1, te2)) |-> te3)"
      " else n3++;\n"
      "  assert property (@(posedge clk) (te1 ##[1:3] te2) |-> te3)"
      " else n4++;\n",
      EarliestDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "n1"), 0u);
  EXPECT_EQ(VarValue(f, "n2"), 0u);
  EXPECT_EQ(VarValue(f, "n3"), 0u);
  EXPECT_EQ(VarValue(f, "n4"), 1u);
}

TEST(FirstMatchItems, ALocalTakesItsValueFromTheFirstMatch) {
  std::string src = SequenceCoverSource(
      TickCounter() +
          "  int n1 = 0, n2 = 0, n3 = 0;\n"
          "  property p1; int v;"
          " first_match(te1 ##[1:3] te2, v = tick) |-> v == 2; endproperty\n"
          "  property p2; int v;"
          " first_match((te1 ##[1:3] te2, v = tick)) |-> v == 2;"
          " endproperty\n"
          "  property p3; int v, w;"
          " first_match(te1 ##[1:3] te2, v = tick, w = v + 10) |-> w == 12;"
          " endproperty\n"
          "  assert property (@(posedge clk) p1) else n1++;\n"
          "  assert property (@(posedge clk) p2) else n2++;\n"
          "  assert property (@(posedge clk) p3) else n3++;\n",
      EarliestDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "n1"), 0u);
  EXPECT_EQ(VarValue(f, "n2"), 0u);
  EXPECT_EQ(VarValue(f, "n3"), 0u);
}

TEST(FirstMatchItems, ACallRunsOnceAtTheFirstMatch) {
  std::string src = SequenceCoverSource(
      "  int bumps = 0;\n"
      "  function void bump(); bumps++; endfunction\n"
      "  c1: cover property (@(posedge clk)"
      " first_match(te1 ##[1:3] te2, bump()));\n",
      EarliestDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "bumps"), 1u);
}

TEST(FirstMatchCoverSequence, DISABLED_ACoverSequenceKeepsOnlyTheEarliestEnd) {
  std::string src = SequenceCoverSource(
      "  int bumps = 0;\n"
      "  function void bump(); bumps++; endfunction\n"
      "  sequence sn; first_match(te1 ##[1:3] te2); endsequence\n"
      "  sequence sx(x); first_match(x ##[1:3] te2); endsequence\n"
      "  c1: cover sequence (@(posedge clk)"
      " first_match(te1 ##[1:3] te2)) at = $time;\n"
      "  c2: cover sequence (@(posedge clk)"
      " first_match(te1 ##[1:3] te2, bump()));\n"
      "  c3: cover sequence (@(posedge clk) sn);\n"
      "  c4: cover sequence (@(posedge clk) sx(te1));\n",
      EarliestDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 25u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(VarValue(f, "bumps"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 1u);
}

TEST(FirstMatchItems, DISABLED_MatchesTiedAtTheEarliestEndAreAllKept) {
  std::string src = SequenceCoverSource(
      "  int ties = 0, tied_at = 0;\n"
      "  function void tie(); ties++; tied_at = $time; endfunction\n"
      "  c1: cover sequence (@(posedge clk)"
      " first_match((te1 ##[2:3] te2) or (te3 ##[1:2] te4))) at = $time;\n"
      "  cover property (@(posedge clk)"
      " first_match((te1 ##[2:3] te2) or (te3 ##[1:2] te4), tie()));\n",
      DriveTicks({{1}, {3, 4}, {1}, {3}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(VarValue(f, "at"), 25u);
  EXPECT_EQ(VarValue(f, "ties"), 2u);
  EXPECT_EQ(VarValue(f, "tied_at"), 25u);
}

TEST(FirstMatchPlaces, EveryDesignElementKeepsTheEarliestEnd) {
  std::string src = DesignElementCoverSource(
      "cover property (@(posedge clk) first_match(te1 ##[1:3] te2) |->"
      " te3);\n",
      EarliestDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 1u);
}

TEST(FirstMatchPlaces, AProceduralAssertionOverAnInstanceKeepsTheEarliestEnd) {
  std::string src = SequenceCoverSource(
      "  sequence sm(x, y); x ##[1:3] y; endsequence\n"
      "  always @(posedge clk) begin\n"
      "    c1: cover property (first_match(sm(te1, te2)) |-> te3);\n"
      "    c2: cover property (sm(te1, te2) |-> te3);\n"
      "  end\n",
      EarliestDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 0u);
}

TEST(FirstMatchConsequent, EveryDirectiveTakesItAsAConsequent) {
  std::string items =
      "  property pi; te1 |-> first_match(##[1:3] te2); endproperty\n"
      "  property pn; te1 |=> first_match(##[0:2] te2); endproperty\n";
  for (const char* directive : {"assert", "assume"}) {
    for (const char* prop : {"pi", "pn"}) {
      items += "  ";
      items += directive;
      items += " property (@(posedge clk) ";
      items += prop;
      items += ") else fails++;\n";
    }
  }
  items +=
      "  c1: cover property (@(posedge clk) pi);\n"
      "  c2: cover property (@(posedge clk) pn);\n";
  std::string src = SequenceCoverSource(items, DriveTicks({{1, 6}, {3}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 4u);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

TEST(FirstMatchOperands, DISABLED_ASequenceFormalIsTheOperand) {
  std::string src = SequenceCoverSource(
      "  sequence sq(sequence q); first_match(q ##[0:3] te2); endsequence\n"
      "  sequence su(q); first_match(q ##[0:3] te2); endsequence\n"
      "  c1: cover property (@(posedge clk) sq(te1) |-> te3);\n"
      "  c2: cover property (@(posedge clk) su(te1) |-> te3);\n",
      EarliestDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

std::string PlacementDrive() { return DriveTicks({{1}, {2, 3}, {3, 4, 5}}); }

TEST(FirstMatchPlacement, DISABLED_AroundACycleDelay) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " te1 ##1 first_match(te2 ##[1:2] te3)) at = $time;\n"
      "  c2: cover sequence (@(posedge clk)"
      " first_match(te1 ##[1:2] te2) ##1 te3);\n"
      "  c3: cover sequence (@(posedge clk)"
      " te1 ##[1:2] first_match(te2 ##[0:1] te3));\n"
      "  c4: cover sequence (@(posedge clk)"
      " ##1 first_match(te2 ##[0:1] te3));\n",
      PlacementDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 25u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 2u);
}

TEST(FirstMatchPlacement, AsTheLeftOperandOfAnd) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " first_match(te1 ##[1:2] te2) and (te1 ##2 te3));\n",
      PlacementDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(FirstMatchPlacement, OnTheOtherSideOfAndAndOr) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " (te1 ##2 te3) and first_match(te1 ##[1:2] te2));\n"
      "  c2: cover property (@(posedge clk)"
      " first_match(te1 ##[1:2] te2) or (te1 ##2 te3));\n",
      PlacementDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

TEST(FirstMatchPlacement, DISABLED_AsTheLeftOperandOfABareIntersect) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk)"
      " first_match(te1 ##[1:2] te2) intersect (te1 ##1 1));\n",
      PlacementDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(FirstMatchPlacement, DISABLED_AsAnOperandOfASequenceOperator) {
  std::string src = SequenceCoverSource(
      "  c2: cover sequence (@(posedge clk)"
      " (first_match(te1 ##[1:2] te2) or (te1 ##2 te3)));\n"
      "  c3: cover sequence (@(posedge clk)"
      " (te1 ##[1:2] te2) intersect first_match(te1 ##[1:2] te2));\n"
      "  c4: cover property (@(posedge clk)"
      " first_match(te2 ##[0:1] te3) within (te1 ##4 te3));\n"
      "  c5: cover sequence (@(posedge clk)"
      " te2 throughout first_match(te2 ##[0:2] te3));\n",
      PlacementDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c5:"), 2u);
}

TEST(FirstMatchPlacement, DISABLED_InsideAGroupOrAnotherFirstMatch) {
  std::string src = SequenceCoverSource(
      "  int bumps = 0;\n"
      "  function void bump(); bumps++; endfunction\n"
      "  c1: cover sequence (@(posedge clk)"
      " (first_match(te1 ##[1:2] te2))) at = $time;\n"
      "  c2: cover sequence (@(posedge clk)"
      " (first_match(te1 ##[1:2] te2), bump()));\n"
      "  c3: cover sequence (@(posedge clk)"
      " first_match(first_match(te1 ##[1:2] te2) ##1 te3));\n",
      PlacementDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 15u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(VarValue(f, "bumps"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
}

TEST(FirstMatchPlacement, DISABLED_InADeclarationOutsideTheAssertion) {
  std::string src = SequenceCoverSource(
      "  sequence sd(x, y, z); x ##1 first_match(y ##[1:2] z); endsequence\n"
      "  property pd; first_match(te1 ##[1:2] te2) ##1 te3; endproperty\n"
      "  c1: cover sequence (@(posedge clk) sd(te1, te2, te3));\n"
      "  c2: cover sequence (@(posedge clk) pk::pf(te1, te2, te3));\n"
      "  c3: cover property (@(posedge clk) pd);\n",
      PlacementDrive(),
      "package pk;\n"
      "  sequence pf(x, y, z); x ##1 first_match(y ##[1:2] z); endsequence\n"
      "endpackage\n");
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
}

}  // namespace
