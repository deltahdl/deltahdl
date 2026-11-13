#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

std::string IndexDrive() { return DriveTicks({{1, 2, 3}, {2}}); }

std::string IndexSource(const std::string& items,
                        const std::string& outside = "") {
  return SequenceCoverSource(
      "  logic [7:0] vec = 8'b1010_0110;\n"
      "  int arr [4] = '{10, 20, 30, 40};\n"
      "  logic [7:0] dn [0:3] = '{8'h01, 8'h02, 8'h04, 8'h08};\n"
      "  int da [] = '{11, 22, 33};\n"
      "  int q [$] = '{44, 55, 66};\n"
      "  int aa [int] = '{2: 77, 3: 88};\n"
      "  function int dbl(int y); return 2 * y; endfunction\n" +
          items,
      IndexDrive(), outside);
}

void ExpectSequenceCovers(const std::string& items, int covers,
                          const std::string& outside = "") {
  std::string src = IndexSource(items, outside);
  SimFixture f;
  RunSequenceDesign(src, f);
  for (int i = 1; i <= covers; ++i) {
    std::string label = "c" + std::to_string(i) + ":";
    EXPECT_EQ(CoverCount(f, src, label), 2u) << label;
  }
}

std::string PropertyItems(const std::string& locals,
                          const std::string& antecedent_items,
                          const std::string& consequent) {
  std::string decl = "  property pr; " + locals + " @(posedge clk) (te1, " +
                     antecedent_items + ") |-> " + consequent +
                     "; endproperty\n";
  return decl +
         "  c1: cover property (pr);\n"
         "  assert property (pr) else fails++;\n";
}

void ExpectPropertyCounts(const std::string& locals,
                          const std::string& antecedent_items,
                          const std::string& consequent) {
  std::string src =
      IndexSource(PropertyItems(locals, antecedent_items, consequent));
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(VarValue(f, "fails"), 1u);
}

TEST(LocalIndex, ABitSelectOfAVectorReadsTheBitTheLocalNames) {
  ExpectSequenceCovers(
      "  sequence sb; int i; @(posedge clk) (te1, i = 2 + te2) ##1 vec[i];"
      " endsequence\n"
      "  c1: cover sequence (sb);\n",
      1);
  ExpectPropertyCounts("int i;", "i = 2 + te2", "##1 vec[i]");
}

TEST(LocalIndex, AnIndexedPartSelectStartsAtTheLocal) {
  ExpectSequenceCovers(
      "  sequence su; int i;\n"
      "    @(posedge clk) (te1, i = 4 - te2) ##1 (vec[i+:4] == 4'b1010);\n"
      "  endsequence\n"
      "  sequence sd; int i;\n"
      "    @(posedge clk) (te1, i = 7 - te2) ##1 (vec[i-:4] == 4'b1010);\n"
      "  endsequence\n"
      "  c1: cover sequence (su);\n"
      "  c2: cover sequence (sd);\n",
      2);
  ExpectPropertyCounts("int i;", "i = 4 - te2", "##1 (vec[i+:4] == 4'b1010)");
  ExpectPropertyCounts("int i;", "i = 7 - te2", "##1 (vec[i-:4] == 4'b1010)");
}

TEST(LocalIndex, AnArithmeticIndexReadsTheBitItComputes) {
  ExpectSequenceCovers(
      "  sequence sa; int i;\n"
      "    @(posedge clk) (te1, i = 1 + te2) ##1"
      " (vec[i*2+1] == 0 && vec[i+1]);\n"
      "  endsequence\n"
      "  c1: cover sequence (sa);\n",
      1);
  ExpectPropertyCounts("int i;", "i = 1 + te2",
                       "##1 (vec[i*2+1] == 0 && vec[i+1])");
}

TEST(LocalIndex, AFixedArrayElementIsTheOneTheLocalsName) {
  ExpectSequenceCovers(
      "  sequence sf; int i;\n"
      "    @(posedge clk) (te1, i = 2 + te2) ##1 (arr[i] == 30);\n"
      "  endsequence\n"
      "  sequence sm; int i, j;\n"
      "    @(posedge clk) (te1, i = 2, j = 2 + te2) ##1 dn[i][j];\n"
      "  endsequence\n"
      "  c1: cover sequence (sf);\n"
      "  c2: cover sequence (sm);\n",
      2);
  ExpectPropertyCounts("int i;", "i = 2 + te2", "##1 (arr[i] == 30)");
  ExpectPropertyCounts("int i, j;", "i = 2, j = 2 + te2", "##1 dn[i][j]");
}

TEST(LocalIndex, AVariableSizeArrayElementIsTheOneTheLocalNames) {
  ExpectSequenceCovers(
      "  sequence sd; int i;\n"
      "    @(posedge clk) (te1, i = 2 - te2) ##1 (da[i] == 33);\n"
      "  endsequence\n"
      "  sequence sq; int i;\n"
      "    @(posedge clk) (te1, i = 2 - te2) ##1 (q[i] == 66);\n"
      "  endsequence\n"
      "  sequence sa; int i;\n"
      "    @(posedge clk) (te1, i = 2 + te2) ##1 (aa[i] == 77);\n"
      "  endsequence\n"
      "  c1: cover sequence (sd);\n"
      "  c2: cover sequence (sq);\n"
      "  c3: cover sequence (sa);\n",
      3);
  ExpectPropertyCounts("int i;", "i = 2 - te2", "##1 (da[i] == 33)");
  ExpectPropertyCounts("int i;", "i = 2 - te2", "##1 (q[i] == 66)");
  ExpectPropertyCounts("int i;", "i = 2 + te2", "##1 (aa[i] == 77)");
}

TEST(LocalIndex, ABitOfAPackedLocalIsTheOneAnotherLocalNames) {
  ExpectSequenceCovers(
      "  sequence sl; logic [7:0] lv; int i;\n"
      "    @(posedge clk) (te1, lv = 8'b0000_0100, i = 2 + te2) ##1 lv[i];\n"
      "  endsequence\n"
      "  c1: cover sequence (sl);\n",
      1);
  ExpectPropertyCounts("logic [7:0] lv; int i;",
                       "lv = 8'b0000_0100, i = 2 + te2", "##1 lv[i]");
}

TEST(LocalIndex, DISABLED_AnElementOfAnUnpackedLocalIsTheOneAnotherLocalNames) {
  ExpectSequenceCovers(
      "  sequence sl; int la [4]; int i;\n"
      "    @(posedge clk) (te1, la[2] = 30, i = 2 + te2) ##1 (la[i] == 30);\n"
      "  endsequence\n"
      "  c1: cover sequence (sl);\n",
      1);
  ExpectPropertyCounts("int la [4]; int i;", "la[2] = 30, i = 2 + te2",
                       "##1 (la[i] == 30)");
}

TEST(LocalIndex, AnIndexedReadFeedsALaterLocalAMatchItemAndAnInstance) {
  ExpectSequenceCovers(
      "  sequence si; int i = 2 + te2; int j = arr[i];\n"
      "    @(posedge clk) te1 ##1 (j == 30);\n"
      "  endsequence\n"
      "  sequence sr; int i, j;\n"
      "    @(posedge clk) (te1, i = 2 + te2, j = arr[i]) ##1 (j == 30);\n"
      "  endsequence\n"
      "  sequence sk(k); vec[k]; endsequence\n"
      "  sequence sn; int i;\n"
      "    @(posedge clk) (te1, i = 2 + te2) ##1 sk(i);\n"
      "  endsequence\n"
      "  c1: cover sequence (si);\n"
      "  c2: cover sequence (sr);\n"
      "  c3: cover sequence (sn);\n",
      3);
  ExpectPropertyCounts("int i, j;", "i = 2 + te2, j = arr[i]", "##1 (j == 30)");
}

TEST(LocalIndex, APropertyIfConditionReadsTheBitTheLocalNames) {
  std::string src = IndexSource(
      "  property pf; int i;\n"
      "    @(posedge clk) (te1, i = 2 + te2) |=> if (vec[i]) 1 else 0;\n"
      "  endproperty\n"
      "  c1: cover property (pf);\n"
      "  assert property (pf) else fails++;\n");
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
  EXPECT_EQ(VarValue(f, "fails"), 1u);
}

TEST(LocalOperand, EachKindOfOperatorAndCallTakesALocal) {
  ExpectSequenceCovers(
      "  sequence sc; logic [3:0] hi, x;\n"
      "    @(posedge clk) (te1, hi = 4'hA, x = 4'h5 + te2) ##1"
      " ({hi, x} == 8'hA5);\n"
      "  endsequence\n"
      "  sequence sq; int x;\n"
      "    @(posedge clk) (te1, x = te2 ? 1 : 3) ##1 ((x > 2 ? 7 : 9) == 7);\n"
      "  endsequence\n"
      "  sequence sf; int x;\n"
      "    @(posedge clk) (te1, x = 3 + te2) ##1 (dbl(x) == 6);\n"
      "  endsequence\n"
      "  sequence ss; logic [3:0] x;\n"
      "    @(posedge clk) (te1, x = 3 + te2) ##1 ($countones(x) == 2);\n"
      "  endsequence\n"
      "  c1: cover sequence (sc);\n"
      "  c2: cover sequence (sq);\n"
      "  c3: cover sequence (sf);\n"
      "  c4: cover sequence (ss);\n",
      4);
  ExpectPropertyCounts("logic [3:0] hi, x;", "hi = 4'hA, x = 4'h5 + te2",
                       "##1 ({hi, x} == 8'hA5)");
  ExpectPropertyCounts("int x;", "x = te2 ? 1 : 3",
                       "##1 ((x > 2 ? 7 : 9) == 7)");
  ExpectPropertyCounts("int x;", "x = 3 + te2", "##1 (dbl(x) == 6)");
  ExpectPropertyCounts("logic [3:0] x;", "x = 3 + te2",
                       "##1 ($countones(x) == 2)");
}

constexpr char kElementSequence[] =
    "cover sequence (sb);\n"
    "  logic [7:0] vec = 8'b1010_0110;\n"
    "  sequence sb; int i; @(posedge clk) (te1, i = 2 + te2) ##1 vec[i];"
    " endsequence\n";

constexpr char kElementProperty[] =
    "cover property (pb);\n"
    "  logic [7:0] vec = 8'b1010_0110;\n"
    "  property pb; int i; @(posedge clk) (te1, i = 2 + te2) |-> ##1 vec[i];"
    " endproperty\n";

void ExpectEachElementTwice(const char* statement) {
  std::string src = DesignElementCoverSource(statement, IndexDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  for (const char* label : {"i1:", "p1:", "k1:", "g1:"}) {
    EXPECT_EQ(CoverCount(f, src, label), 2u) << label;
  }
}

TEST(LocalIndexPlaces, ASequenceInEveryDesignElementReadsTheBitTheLocalNames) {
  ExpectEachElementTwice(kElementSequence);
}

TEST(LocalIndexPlaces, APropertyInEveryDesignElementReadsTheBitTheLocalNames) {
  ExpectEachElementTwice(kElementProperty);
}

constexpr char kOutsideIndex[] =
    "package pk;\n"
    "  sequence ps(v, a, b); int i; (a, i = 2 + b) ##1 v[i]; endsequence\n"
    "  property pp(v, a, b); int i; (a, i = 2 + b) |-> ##1 v[i];"
    " endproperty\n"
    "endpackage\n"
    "sequence us(v, a, b); int i; (a, i = 2 + b) ##1 v[i]; endsequence\n"
    "property up(v, a, b); int i; (a, i = 2 + b) |-> ##1 v[i]; endproperty\n";

TEST(LocalIndexPlaces, APackageSequenceAndPropertyReadTheBitTheLocalNames) {
  ExpectSequenceCovers(
      "  c1: cover sequence (@(posedge clk) pk::ps(vec, te1, te2));\n"
      "  c2: cover property (@(posedge clk) pk::pp(vec, te1, te2));\n",
      2, kOutsideIndex);
}

TEST(LocalIndexPlaces,
     DISABLED_ACompilationUnitSequenceAndPropertyReadTheBitTheLocalNames) {
  ExpectSequenceCovers(
      "  c1: cover sequence (@(posedge clk) us(vec, te1, te2));\n"
      "  c2: cover property (@(posedge clk) up(vec, te1, te2));\n",
      2, kOutsideIndex);
}

std::string FlowSource(const std::string& items) {
  return SequenceCoverSource(
      "  sequence sub(lv); (te2, lv = 3); endsequence\n"
      "  sequence sub2(lv); (te2, lv = 3) ##1 (1, lv += 4); endsequence\n" +
          items,
      DriveTicks({{1, 5}, {2, 6}}));
}

void ExpectEachCoverTwice(const std::string& src, int covers) {
  SimFixture f;
  RunSequenceDesign(src, f);
  for (int i = 1; i <= covers; ++i) {
    std::string label = "c" + std::to_string(i) + ":";
    EXPECT_EQ(CoverCount(f, src, label), 2u) << label;
  }
}

TEST(LocalThroughInstance, APropertyLocalPassedWholeTakesTheInstancesValue) {
  ExpectEachCoverTwice(
      FlowSource(
          "  property pa; int v;\n"
          "    @(posedge clk) (te1, v = 0) ##1 sub(v) |-> ##1 (v == 3);\n"
          "  endproperty\n"
          "  property pc; int v;\n"
          "    @(posedge clk) te1 ##1 sub(v) |-> (v == 3);\n"
          "  endproperty\n"
          "  c1: cover property (pa);\n"
          "  c2: cover property (pc);\n"),
      2);
}

TEST(LocalThroughInstance, ALocalFormalPassedWholeTakesTheInstancesValue) {
  ExpectEachCoverTwice(
      FlowSource("  sequence sl(local input int v);\n"
                 "    te1 ##1 sub(v) ##1 (v == 3);\n"
                 "  endsequence\n"
                 "  c1: cover sequence (@(posedge clk) sl(0));\n"),
      1);
}

TEST(LocalThroughInstance, TheLastOfSeveralAssignmentsFlowsOut) {
  ExpectEachCoverTwice(
      FlowSource("  sequence sm; int v;\n"
                 "    @(posedge clk) te1 ##1 sub2(v) ##1 (v == 7);\n"
                 "  endsequence\n"
                 "  c1: cover sequence (sm);\n"),
      1);
}

}  // namespace
