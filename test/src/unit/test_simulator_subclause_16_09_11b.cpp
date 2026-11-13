#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

std::string EndDrive() { return DriveTicks({{1}, {2}, {3}, {4}, {1}}); }

constexpr const char* kEnds =
    "  sequence e1; @(posedge clk) te1 ##1 te2; endsequence\n"
    "  sequence e2(x, y); @(posedge clk) x ##1 y; endsequence\n";

std::string ForEachInstance() {
  std::string items;
  int n = 0;
  for (const char* inst : {"e1", "e2(te1, te2)"}) {
    for (const char* form :
         {".triggered ##1 te3", ".triggered", ".triggered ##0 te2",
          ".triggered[*1] ##1 te3", ".triggered |=> te3", ".triggered |-> te2",
          ".triggered && te2", "te1 ##1 "}) {
      std::string spec;
      if (std::string(form) == "te1 ##1 ") {
        spec = form;
        spec += inst;
        spec += ".triggered";
      } else {
        spec = inst;
        spec += form;
      }
      items += "  c";
      items += std::to_string(++n);
      items += ": cover property (@(posedge clk) ";
      items += spec;
      items += ");\n";
    }
  }
  return items;
}

void ExpectEachCoverOnce(const std::string& src, int first, int last) {
  SimFixture f;
  RunSequenceDesign(src, f);
  for (int n = first; n <= last; ++n) {
    std::string label = "c" + std::to_string(n) + ":";
    EXPECT_EQ(CoverCount(f, src, label), 1u) << label;
  }
}

TEST(TriggeredOperands, AnInstanceWithoutArgumentsEndsInEveryForm) {
  std::string src =
      SequenceCoverSource(std::string(kEnds) + ForEachInstance(), EndDrive());
  ExpectEachCoverOnce(src, 1, 8);
}

TEST(TriggeredOperands, AnInstanceWithArgumentsEndsAloneOrInABoolean) {
  std::string src =
      SequenceCoverSource(std::string(kEnds) + ForEachInstance(), EndDrive());
  ExpectEachCoverOnce(src, 10, 10);
  ExpectEachCoverOnce(src, 15, 15);
}

TEST(TriggeredOperands, DISABLED_AnInstanceWithArgumentsEndsInEveryForm) {
  std::string src =
      SequenceCoverSource(std::string(kEnds) + ForEachInstance(), EndDrive());
  ExpectEachCoverOnce(src, 9, 16);
}

TEST(TriggeredOperands, AWaitResumesAtTheEndPoint) {
  std::string src = SequenceCoverSource(
      std::string(kEnds) +
          "  int w1 = 0;\n"
          "  int cat = 0;\n"
          "  initial begin wait (e1.triggered); w1 = $time;"
          " cat = {e1.triggered, e1.triggered, 1'b0}; end\n",
      EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "w1"), 15u);
  EXPECT_EQ(VarValue(f, "cat"), 6u);
}

TEST(TriggeredOperands, DISABLED_AWaitOnAnInstanceWithArgumentsResumes) {
  std::string src = SequenceCoverSource(
      std::string(kEnds) +
          "  int w2 = 0;\n"
          "  initial begin wait (e2(te1, te2).triggered); w2 = $time; end\n",
      EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "w2"), 15u);
}

std::string CheckerOfUntyped() {
  return "checker chk(untyped s, logic clk);\n"
         "  int hits = 0;\n"
         "  always_ff @(posedge clk) if (s.triggered) hits <= hits + 1;\n"
         "endchecker\n";
}

TEST(TriggeredOperands, UntypedFormalsBoundToAnInstanceWithoutArguments) {
  std::string src = SequenceCoverSource(
      std::string(kEnds) +
          "  sequence eu1(q); @(posedge clk) q.triggered ##1 te3;"
          " endsequence\n"
          "  sequence eus(q); @(posedge clk) q.triggered; endsequence\n"
          "  property pu(q); @(posedge clk) q.triggered |=> te3; endproperty\n"
          "  c1: cover property (eu1(e1));\n"
          "  c2: cover property (eus(e1));\n"
          "  c3: cover property (pu(e1));\n",
      EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
}

TEST(TriggeredOperands, ACheckerAloneReadsItsUntypedFormal) {
  std::string src =
      SequenceCoverSource(std::string(kEnds) + "  chk k1(e1, clk);\n",
                          EndDrive(), CheckerOfUntyped());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "k1.hits"), 1u);
}

TEST(TriggeredOperands, DISABLED_ACheckerActualLeavesTheOtherReadersTheirEnds) {
  std::string src = SequenceCoverSource(
      std::string(kEnds) +
          "  c1: cover property (@(posedge clk) e1.triggered ##1 te3);\n"
          "  c2: cover property (@(posedge clk) e1.triggered);\n"
          "  chk k1(e1, clk);\n",
      EndDrive(), CheckerOfUntyped());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(VarValue(f, "k1.hits"), 1u);
}

TEST(TriggeredOperands, DISABLED_UntypedFormalsBoundToAnInstanceWithArguments) {
  std::string src = SequenceCoverSource(
      std::string(kEnds) +
          "  sequence eu1(q); @(posedge clk) q.triggered ##1 te3;"
          " endsequence\n"
          "  sequence eus(q); @(posedge clk) q.triggered; endsequence\n"
          "  property pu(q); @(posedge clk) q.triggered |=> te3; endproperty\n"
          "  c1: cover property (eu1(e2(te1, te2)));\n"
          "  c2: cover property (eus(e2(te1, te2)));\n"
          "  c3: cover property (pu(e2(te1, te2)));\n"
          "  chk k2(e2(te1, te2), clk);\n",
      EndDrive(), CheckerOfUntyped());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
  EXPECT_EQ(VarValue(f, "k2.hits"), 1u);
}

constexpr const char* kE3 =
    "  sequence e3(sequence a, untyped b);\n"
    "    @(posedge clk) a.triggered ##1 b;\n"
    "  endsequence\n";

TEST(TriggeredOperands, ASequenceFormalBoundToAnInstance) {
  std::string src =
      SequenceCoverSource(std::string(kEnds) + kE3 +
                              "  c1: cover property (@(posedge clk) te5 ##1 "
                              "e3(e1, te3) ##1 te4);\n",
                          EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(TriggeredOperands,
     DISABLED_ASequenceFormalBoundToAnInstanceWithArguments) {
  std::string src = SequenceCoverSource(
      std::string(kEnds) + kE3 +
          "  c1: cover property (@(posedge clk) te5 ##1 e3(e2(te1, te2), te3)"
          " ##1 te4);\n",
      EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(TriggeredOperands, DISABLED_TheClausesRule3BindsASequenceExpression) {
  std::string src = SequenceCoverSource(
      std::string(kE3) +
          "  c1: cover property (@(posedge clk)"
          " te5 ##1 e3(te1 ##1 te2, te3) ##1 te4);\n"
          "  c2: cover property (@(posedge clk) e3(te1 ##1 te2, te3));\n"
          "  c3: cover property (e3(te1 ##1 te2, te3));\n",
      EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
}

TEST(TriggeredOperands, DISABLED_PackageAndHierarchicalInstancesWithArguments) {
  std::string src = SequenceCoverSource(
      "  ifc i(clk);\n"
      "  c1: cover property (@(posedge clk) pk::ps(te1, te2).triggered);\n"
      "  c2: cover property (@(posedge clk) pk::pc(clk, te1, te2).triggered);\n"
      "  c3: cover property (@(posedge clk) i.ei(te1, te2).triggered);\n"
      "  c4: cover property (@(posedge clk)"
      " pk::ps(te1, te2).triggered ##1 te3);\n",
      EndDrive(),
      "package pk;\n"
      "  sequence ps(x, y); x ##1 y; endsequence\n"
      "  sequence pc(clock, x, y); @(posedge clock) x ##1 y; endsequence\n"
      "endpackage\n"
      "interface ifc(input logic clk);\n"
      "  sequence ei(x, y); @(posedge clk) x ##1 y; endsequence\n"
      "endinterface\n");
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 1u);
}

TEST(TriggeredOperands, AClocklessModuleInstanceWithArgumentsAlone) {
  std::string src = SequenceCoverSource(
      "  sequence ec(x, y); x ##1 y; endsequence\n"
      "  c1: cover property (@(posedge clk) ec(te1, te2).triggered);\n",
      EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(TriggeredOperands,
     DISABLED_AClocklessModuleInstanceWithArgumentsThenMore) {
  std::string src = SequenceCoverSource(
      "  sequence ec(x, y); x ##1 y; endsequence\n"
      "  c1: cover property (@(posedge clk) ec(te1, te2).triggered ##1 te3);\n",
      EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(TriggeredOperands, EveryDesignElementReadsAnInstanceWithArgumentsAlone) {
  std::string src = DesignElementCoverSource(
      "cover property (@(posedge clk) ew(te1, te2).triggered);\n"
      "  sequence ew(x, y); @(posedge clk) x ##1 y; endsequence\n",
      EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 1u);
}

TEST(TriggeredOperands,
     DISABLED_EveryDesignElementReadsAnInstanceWithArgumentsThenMore) {
  std::string src = DesignElementCoverSource(
      "cover property (@(posedge clk) ew(te1, te2).triggered ##1 te3);\n"
      "  sequence ew(x, y); @(posedge clk) x ##1 y; endsequence\n",
      EndDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "g1:"), 1u);
}

TEST(TriggeredEmptyMatch, AnEmptyMatchSetsNoTriggered) {
  std::string src = SequenceCoverSource(
      "  sequence zr; @(posedge clk) te1[*0:1]; endsequence\n"
      "  sequence zn; @(posedge clk) te2[*0]; endsequence\n"
      "  int wz = 0;\n"
      "  initial begin wait (zr.triggered); wz = $time; end\n"
      "  c1: cover property (@(posedge clk) zr.triggered);\n"
      "  c2: cover property (@(posedge clk) zn.triggered);\n"
      "  c3: cover property (@(posedge clk) zr.triggered ##1 te2);\n",
      DriveTicks({{3}, {4}}));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 0u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
  EXPECT_EQ(VarValue(f, "wz"), 25u);
}

}  // namespace
