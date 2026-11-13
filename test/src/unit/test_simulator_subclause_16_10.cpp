#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_sampling_bench.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SequenceLocals, InitializationAssignmentsRunInDeclarationOrder) {
  const std::string kLocals = "    int v = te1, w = v + 1;\n";
  SimFixture f;
  auto* set = RunAndFindVar(
      SequenceTickSource("te2 ##1 (w == 2)", DriveTicks({{3}, {3}, {}, {}, {}}),
                         "", kLocals),
      f, "hits");
  ASSERT_NE(set, nullptr);
  EXPECT_EQ(set->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
  SimFixture g;
  auto* clear = RunAndFindVar(
      SequenceTickSource("te2 ##1 (w == 2)", DriveTicks({{}, {3}, {}, {}, {}}),
                         "", kLocals),
      g, "hits");
  ASSERT_NE(clear, nullptr);
  EXPECT_EQ(clear->value.ToUint64(), 0u);
}

void ExpectOneEnd(const std::string& body, const std::string& locals,
                  const std::vector<std::vector<int>>& drive, uint64_t last,
                  const std::string& prelude = "") {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource(body, DriveTicks(drive), prelude, locals), f, "hits");
  ASSERT_NE(hits, nullptr) << body;
  EXPECT_EQ(hits->value.ToUint64(), 1u) << body;
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), last) << body;
}

void ExpectOneEndAtFour(const std::string& body, const std::string& locals,
                        const std::string& prelude = "") {
  ExpectOneEnd(body, locals, {{}, {3}, {}, {}, {}}, 35, prelude);
}

void ExpectOneEndAfterTe2(const std::string& last_operand,
                          const std::string& locals,
                          const std::string& prelude = "") {
  ExpectOneEndAtFour("te2 ##1 " + last_operand, locals, prelude);
}

TEST(SequenceLocals, APackedLocalHoldsItsDeclaredWidth) {
  ExpectOneEndAfterTe2("(x == 13)", "    logic [3:0] x = 29;\n");
}

TEST(SequenceLocals, AnIntLocalReadsAsSigned) {
  ExpectOneEndAfterTe2("(x < 0)", "    int x = -1;\n");
  ExpectOneEndAfterTe2("y", "    int x = -1;\n    bit y = x < 0;\n");
}

TEST(SequenceLocals, ALocalTakesTheSignednessItsKeywordWrites) {
  ExpectOneEndAfterTe2("(x < 0)", "    logic signed [3:0] x = -1;\n");
  ExpectOneEndAfterTe2("(x > 0)", "    int unsigned x = -1;\n");
}

constexpr char kNibbleTypes[] =
    "  typedef logic [3:0] nib_t;\n"
    "  typedef logic signed [3:0] snib_t;\n"
    "  typedef bit [3:0] bnib_t;\n";

TEST(SequenceLocals, ALocalOfATypeNameIsTheTypeTheNameStandsFor) {
  ExpectOneEndAfterTe2("(x == 13)", "    nib_t x = 29;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("$isunknown(x)", "    nib_t x = 'x;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("(x == 0)", "    bnib_t x = 'x;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("(x < 0)", "    snib_t x = -1;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("(x == 255)", "    nib_t [1:0] x = 9'h1FF;\n",
                       kNibbleTypes);
}

TEST(SequenceLocals, AMatchItemAssignsASelectOfTheLocal) {
  struct Case {
    const char* item;
    const char* want;
  };
  const Case kCases[] = {{"v[1] = 0", "8'h1D"},
                         {"v[7:6] = 2'b11", "8'hDF"},
                         {"v[3:0] += 3", "8'h12"},
                         {"v[7:4]++", "8'h2F"},
                         {"--v[4]", "8'h0F"}};
  for (const Case& c : kCases) {
    ExpectOneEndAtFour(
        std::string("(te2, ") + c.item + ") ##1 (v == " + c.want + ")",
        "    logic [7:0] v = 8'h1F;\n");
  }
}

TEST(SequenceLocals, AMatchItemAssignsASelectOfALocalReachedThroughAnInstance) {
  ExpectOneEndAtFour("sub", "",
                     "  sequence sub; logic [7:0] w = 8'h1F;\n"
                     "    (te2, w[1] = 0) ##1 (w == 8'h1D);\n"
                     "  endsequence\n");
  ExpectOneEndAtFour("sub(v) ##1 (v == 8'h1D)", "    logic [7:0] v = 8'h1F;\n",
                     "  sequence sub(lv); (te2, lv[1] = 0); endsequence\n");
}

constexpr char kPairType[] =
    "  typedef struct packed { logic [3:0] hi, lo; } pair_t;\n";

TEST(SequenceLocals, AStructureLocalReadsAndWritesItsMembers) {
  const std::string kLocal = "    pair_t p = 8'h3C;\n";
  ExpectOneEndAfterTe2("(p.hi == 3 && p.lo == 12)", kLocal, kPairType);
  ExpectOneEndAfterTe2("(h == 3)", kLocal + "    logic [3:0] h = p.hi;\n",
                       kPairType);
  ExpectOneEndAtFour("(te2, p.lo = 5) ##1 (p == 8'h35)", kLocal, kPairType);
  ExpectOneEndAtFour("(te2, p.hi += 1) ##1 (p == 8'h4C)", kLocal, kPairType);
}

TEST(SequenceLocals, ASelectOfALocalResolvesAgainstItsDeclaredDimensions) {
  const std::string kVector = "    logic [8:1] v = 1;\n";
  ExpectOneEndAfterTe2("(v[1] == 1 && v[2] == 0)", kVector);
  ExpectOneEndAfterTe2("b", kVector + "    bit b = v[1];\n");
  ExpectOneEndAtFour("(te2, v[1] = 0) ##1 (v == 0)", kVector);
  ExpectOneEndAfterTe2("(x[1] == 4'hA && x[0] == 4'h5)",
                       "    nib_t [1:0] x = 8'hA5;\n", kNibbleTypes);
  ExpectOneEndAfterTe2("(y[1] == 4'hA && y[0][0] == 1)",
                       "    logic [1:0][3:0] y = 8'hA5;\n");
}

TEST(SequenceLocals, ATwoStateLocalDropsTheUnknownBitsOfItsInitialization) {
  ExpectOneEndAfterTe2("(x == 0)", "    bit [3:0] x = 'x;\n");
  ExpectOneEndAfterTe2("(x == 0)", "    int x = 'z;\n");
}

TEST(SequenceLocals, ATimeLocalIsSixtyFourUnsignedFourStateBits) {
  ExpectOneEndAfterTe2("(t > 64'hFFFF_FFFF)", "    time t = -1;\n");
  ExpectOneEndAfterTe2("$isunknown(t)", "    time t = 'x;\n");
}

TEST(SequenceLocals, MatchItemsRunInOrderAtTheSubsequenceEnd) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      SequenceTickSource("te1 ##1 (te2[->1], x = 1, y = x + 1) ##1 (y == 2)",
                         DriveTicks({{1}, {3}, {}, {}, {}}), "",
                         "    int x, y;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

TEST(SequenceLocals, AssignmentsOnARepeatedOperandAccumulate) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceTickSource("(te1[->1], x += 2)[*3] ##1 (x == 6)",
                                       DriveTicks({{2, 4, 6}, {}, {}, {}, {}}),
                                       "", "    int x = 0;\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 65u);
}

TEST(SequenceLocals, IncrementCountsTheRepeatedCondition) {
  const std::string kBody =
      "($rose(te1), x = 1) ##1 (te1, x++)[*0:$] ##1 !te1 && (x <= 3)";
  SimFixture f;
  auto* three = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{3, 4, 5}, {}, {}, {}, {}}), "",
                         "    int x;\n"),
      f, "hits");
  ASSERT_NE(three, nullptr);
  EXPECT_EQ(three->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
  SimFixture g;
  auto* five = RunAndFindVar(
      SequenceTickSource(kBody, DriveTicks({{3, 4, 5, 6, 7}, {}, {}, {}, {}}),
                         "", "    int x;\n"),
      g, "hits");
  ASSERT_NE(five, nullptr);
  EXPECT_EQ(five->value.ToUint64(), 0u);
}

TEST(SequenceLocals, LocalPassedAsActualIsBoundToTheFormal) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(SequenceTickSource("te1 ##1 sub(v) ##1 (v == 1)",
                                       DriveTicks({{1}, {2}, {}, {}, {}}),
                                       "  sequence sub(lv);\n"
                                       "    (te2, lv = 1);\n"
                                       "  endsequence\n",
                                       "    int v;\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

std::string PropertyLocalSource(const std::string& body,
                                const std::string& decl,
                                const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int v = 0, p = 0, f = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) v <= v + 1;\n" +
         items +
         "  property pr;\n"
         "    " +
         decl +
         ";\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endproperty\n"
         "  assert property (pr) p++; else f++;\n"
         "  initial #100 $finish;\n"
         "endmodule\n";
}

void ExpectPropertyCounts(const std::string& body, uint64_t passes,
                          uint64_t fails, const std::string& decl = "int x",
                          const std::string& items = "") {
  SimFixture f;
  auto* p = RunAndFindVar(PropertyLocalSource(body, decl, items), f, "p");
  ASSERT_NE(p, nullptr) << body;
  EXPECT_EQ(p->value.ToUint64(), passes) << body;
  EXPECT_EQ(f.ctx.FindVariable("f")->value.ToUint64(), fails) << body;
}

TEST(PropertyLocals, AntecedentAssignmentReachesTheConsequent) {
  ExpectPropertyCounts("(1, x = v) |-> ##1 (v == x + 1)", 9, 0);
  ExpectPropertyCounts("(1, x = v) |=> (v == x + 1)", 9, 0);
  ExpectPropertyCounts("(1, x = v) |-> ##1 (v == x + 2)", 0, 9);
}

TEST(PropertyLocals, SequenceBodyReadsItsEarlierAssignment) {
  ExpectPropertyCounts("(1, x = v) ##1 (v == x + 1)", 9, 0);
}

TEST(PropertyLocals, ConsequentReassignsTheLocal) {
  ExpectPropertyCounts("(1, x = v) |-> ##1 (1, x += 1) ##1 (v == x + 1)", 8, 0);
}

TEST(PropertyLocals, EachAttemptHoldsItsOwnCopy) {
  ExpectPropertyCounts("(1, x = v) |-> ##2 (v == x + 2)", 8, 0);
}

TEST(PropertyLocals, APackedLocalHoldsItsDeclaredWidth) {
  ExpectPropertyCounts("(1, x = v + 12) |-> ##1 (x < 12)", 5, 4,
                       "logic [3:0] x");
}

TEST(PropertyLocals, AnIntLocalIsSignedWhateverItIsAssigned) {
  ExpectPropertyCounts("(1, x = 32'hFFFF_FFFF) |-> ##1 (x < 0)", 9, 0);
}

TEST(PropertyLocals, ASignedPackedLocalIsSigned) {
  ExpectPropertyCounts("(1, x = -1) |-> ##1 (x < 0)", 9, 0,
                       "logic signed [3:0] x");
}

TEST(PropertyLocals, ALocalOfATypeNameIsTheTypeTheNameStandsFor) {
  ExpectPropertyCounts("(1, x = v + 12) |-> ##1 (x < 12)", 5, 4, "nib_t x",
                       "  typedef logic [3:0] nib_t;\n");
}

TEST(PropertyLocals, ATimeLocalIsSixtyFourUnsignedBits) {
  ExpectPropertyCounts("(1, x = -1) |-> ##1 (x > 64'hFFFF_FFFF)", 9, 0,
                       "time x");
}

TEST(PropertyLocals, AMatchItemAssignsASelectOfTheLocal) {
  ExpectPropertyCounts("(1, x[0] = 1) |-> ##1 (x == 8'hF1)", 9, 0,
                       "logic [7:0] x = 8'hF0");
  ExpectPropertyCounts("(1, x[3:0] += 2) |-> ##1 (x == 8'hF1)", 9, 0,
                       "logic [7:0] x = 8'hFF");
  ExpectPropertyCounts("(1, x[7:4]++) |-> ##1 (x == 8'h0F)", 9, 0,
                       "logic [7:0] x = 8'hFF");
}

TEST(PropertyLocals, AStructureLocalReadsAndWritesItsMembers) {
  const std::string kDecl = "pair_t x = 8'h3C";
  const std::string kItems =
      "  typedef struct packed { logic [3:0] hi, lo; } pair_t;\n";
  ExpectPropertyCounts("1 |-> ##1 (x.hi == 3 && x.lo == 12)", 9, 0, kDecl,
                       kItems);
  ExpectPropertyCounts("if (x.hi == 3) ##1 1 else ##1 0", 9, 0, kDecl, kItems);
  ExpectPropertyCounts("(1, x.lo = 5) |-> ##1 (x == 8'h35)", 9, 0, kDecl,
                       kItems);
  ExpectPropertyCounts("(1, x.hi += 1) |-> ##1 (x == 8'h4C)", 9, 0, kDecl,
                       kItems);
}

TEST(PropertyLocals, ASelectOfALocalResolvesAgainstItsDeclaredDimensions) {
  ExpectPropertyCounts("1 |-> ##1 (x[1] == 1 && x[2] == 0)", 9, 0,
                       "logic [8:1] x = 1");
  ExpectPropertyCounts("(1, x[1] = 0) |-> ##1 (x == 0)", 9, 0,
                       "logic [8:1] x = 1");
}

TEST(PropertyLocals, ATwoStateLocalHoldsNoUnknownBits) {
  ExpectPropertyCounts("(1, x[0] = 1) |-> ##1 (x == 1)", 9, 0, "bit [3:0] x");
  ExpectPropertyCounts("1 |-> ##1 (x == 0)", 9, 0, "bit [3:0] x = 'x");
}

TEST(PropertyLocals, AMatchItemAssignsALocalAsItsTypeHoldsIt) {
  ExpectPropertyCounts("(1, x = 'x) |-> ##1 (x == 0)", 9, 0, "bit [3:0] x");
  ExpectPropertyCounts("(1, x = 8'hFF) |-> ##1 (x < 0)", 9, 0, "byte x");
}

TEST(PropertyLocals, APackedLocalsCopyIsItsDeclaredWidth) {
  ExpectPropertyCounts("(1, x = v) |-> ##1 ($bits(x) == 4)", 9, 0,
                       "logic [3:0] x");
}

std::string RunTriggeredFlowCase(const std::string& decls) {
  SimFixture f;
  return RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  int cnt = 0;\n"
      "  always @(negedge clk) cnt <= cnt + 1;\n"
      "  int c1 = 0, c2 = 0;\n" +
          decls +
          "  cover property (@(posedge clk) seq_a) c1++;\n"
          "  cover property (@(posedge clk) seq_b) c2++;\n"
          "  initial #97 $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "endmodule\n",
      f);
}

TEST(SequenceLocals, ALocalFlowsOutOfTriggered) {
  std::string out = RunTriggeredFlowCase(
      "  sequence sub(lv, src); @(posedge clk) (1, lv = src) ##1 1;\n"
      "  endsequence\n"
      "  sequence seq_a; int v1, v2;\n"
      "    (sub(v1, cnt).triggered, v2 = v1) ##1 (cnt == v2 + 2);\n"
      "  endsequence\n"
      "  sequence seq_b; int v1;\n"
      "    sub(v1, cnt) ##1 (cnt == v1 + 2);\n"
      "  endsequence\n");
  EXPECT_NE(out.find("c1=8 c2=8\n"), std::string::npos);
}

TEST(SequenceLocals, EachMatchEndingAtTheTickFlowsItsOwnValue) {
  std::string out = RunTriggeredFlowCase(
      "  sequence sub(lv, src); bit w;\n"
      "    @(posedge clk) (1, lv = src, w = 1) ##[1:2] w;\n"
      "  endsequence\n"
      "  sequence seq_a; int v1;\n"
      "    sub(v1, cnt + 0).triggered ##1 (cnt == v1 + 2);\n"
      "  endsequence\n"
      "  sequence seq_b; int v1;\n"
      "    sub(v1, cnt + 0).triggered ##1 (cnt == v1 + 3);\n"
      "  endsequence\n");
  EXPECT_NE(out.find("c1=8 c2=7\n"), std::string::npos);
}

TEST(SequenceLocals, AGroupsItemsAfterARepeatedOperandRunOnce) {
  struct Case {
    const char* group;
    std::vector<int> te2;
    uint64_t last;
  };
  const Case kCases[] = {
      {"(te2[*2], x += 1)", {2, 3}, 35},
      {"(te2[->2], x += 1)", {2, 4}, 45},
  };
  for (const Case& c : kCases) {
    ExpectOneEnd(std::string("(te1, x = 0) ##1 ") + c.group + " ##1 (x == 1)",
                 "    int x;\n", {{1}, c.te2, {}, {}, {}}, c.last);
  }
}

TEST(SequenceLocals, AGroupJoiningSequencesPerformsItsItemsAtItsMatch) {
  struct Case {
    const char* group;
    std::vector<std::vector<int>> drive;
  };
  const Case kCases[] = {
      {"(te1 or te2, x = 1)", {{}, {3}}},
      {"(te1 and te2, x = 1)", {{3}, {3}}},
      {"(te1 ##1 te2 intersect te3[*2], x = 1)", {{2}, {3}, {2, 3}}},
      {"(te1 within te2[*2], x = 1)", {{3}, {2, 3}}},
  };
  for (const Case& c : kCases) {
    ExpectOneEnd(std::string(c.group) + " ##1 (x == 1)", "    int x;\n",
                 c.drive, 35);
  }
}

TEST(SequenceLocals, ARepeatedGroupJoiningSequencesPerformsItsItemsEachTime) {
  for (const char* rep : {"[*2]", "[*1:2]"}) {
    ExpectOneEnd(std::string("(te1 or te2, x += 1)") + rep + " ##1 (x == 2)",
                 "    int x = 0;\n", {{}, {2, 3}}, 35);
  }
}

TEST(SequenceLocals, AGroupPerformsItsItemsAtEachMatchOfAnInstance) {
  const std::string kPrelude =
      "  sequence s; @(posedge clk) te1 ##1 te2; endsequence\n"
      "  sequence t; @(posedge clk) te1 ##1 te2[*2]; endsequence\n"
      "  sequence u; @(posedge clk) te1 or te2; endsequence\n";
  ExpectOneEnd("(s, x = 1) ##1 (x == 1)", "    int x;\n", {{2}, {3}}, 35,
               kPrelude);
  ExpectOneEnd("(t, x += 1) ##1 (x == 1)", "    int x = 0;\n", {{1}, {2, 3}},
               35, kPrelude);
  ExpectOneEnd("(u, x = 1) ##1 (x == 1)", "    int x;\n", {{}, {3}}, 35,
               kPrelude);
  ExpectOneEnd("(s, x += 1)[*2] ##1 (x == 2)", "    int x = 0;\n",
               {{1, 3}, {2, 4}}, 45, kPrelude);
}

TEST(SequenceLocals, DISABLED_ARealLocalHoldsItsInitialValue) {
  for (const char* type : {"real", "shortreal", "realtime"}) {
    const std::string kLocals = std::string("    ") + type + " x = 2.5;\n";
    for (const char* check : {"(x == 2.5)", "(x > 2.0)", "(x < 3.0)"}) {
      ExpectOneEndAfterTe2(check, kLocals);
    }
  }
}

TEST(SequenceLocals, DISABLED_ARealLocalHoldsAMatchItemsValue) {
  ExpectOneEndAtFour("(te2, x = 2.5) ##1 (x == 2.5)", "    real x;\n");
  ExpectOneEndAtFour("(te2, x = 2.5) ##1 (x > 2.0)", "    real x;\n");
}

TEST(SequenceLocals, DISABLED_ARealLocalConvertsToAnIntegralOne) {
  ExpectOneEndAfterTe2("(y == 3)", "    real x = 2.5;\n    int y = x;\n");
}

std::string RealPropertySource(const std::string& check) {
  return "module top;\n"
         "  logic clk = 0, c = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  property pr; real x; (c, x = 2.5) |-> " +
         check +
         "; endproperty\n"
         "  assert property (@(posedge clk) pr) else $display(\"fail %0t\", "
         "$time);\n"
         "  initial begin #10 c = 1; #10 c = 0; #20 $finish; end\n"
         "endmodule\n";
}

TEST(SequenceLocals, DISABLED_ARealPropertyLocalHoldsItsValue) {
  ExpectLines(RealPropertySource("(x == 2.5)"), "fail ", "");
  ExpectLines(RealPropertySource("(x > 2.0)"), "fail ", "");
  ExpectLines(RealPropertySource("(x != 2.5)"), "fail ", "15");
}

std::string TypedLocalSource(const std::string& items) {
  return SequenceCoverSource("  class C; int f; endclass\n" + items,
                             DriveTicks({{1}, {2}}));
}

void ExpectEachCoverOnce(const std::string& src, int covers) {
  SimFixture f;
  RunSequenceDesign(src, f);
  for (int i = 1; i <= covers; ++i) {
    std::string label = "c" + std::to_string(i) + ":";
    EXPECT_EQ(CoverCount(f, src, label), 1u) << label;
  }
}

TEST(TypedLocals, DISABLED_RealLocalsReadInABoolean) {
  ExpectEachCoverOnce(
      TypedLocalSource(
          "  property pr; real r;\n"
          "    @(posedge clk) (te1, r = 1.5) ##1 (te2 && r > 1.25);\n"
          "  endproperty\n"
          "  property ps; shortreal r;\n"
          "    @(posedge clk) (te1, r = 2.5) ##1 (te2 && r > 2.25);\n"
          "  endproperty\n"
          "  property pt; realtime l_t;\n"
          "    @(posedge clk) (te1, l_t = $realtime) ##1"
          " (te2 && $realtime - l_t == 10.0);\n"
          "  endproperty\n"
          "  c1: cover property (pr);\n"
          "  c2: cover property (ps);\n"
          "  c3: cover property (pt);\n"),
      3);
}

TEST(TypedLocals, AClassHandleReadInABoolean) {
  ExpectEachCoverOnce(
      TypedLocalSource(
          "  property ph; C h;\n"
          "    @(posedge clk) (te1, h = null) ##1 (te2 && h == null);\n"
          "  endproperty\n"
          "  c1: cover property (ph);\n"),
      1);
}

TEST(TypedLocals, DISABLED_AStringLocalReadInABoolean) {
  ExpectEachCoverOnce(
      TypedLocalSource(
          "  property pg; string st;\n"
          "    @(posedge clk) (te1, st = \"go\") ##1 (te2 && st == \"go\");\n"
          "  endproperty\n"
          "  c1: cover property (pg);\n"),
      1);
}

TEST(TypedLocals, DISABLED_VariableSizeArrayLocalsReadInABoolean) {
  ExpectEachCoverOnce(
      TypedLocalSource(
          "  property pd; int d [];\n"
          "    @(posedge clk) (te1, d = '{3, 4}) ##1 (te2 && d[1] == 4);\n"
          "  endproperty\n"
          "  property pq; int q [$];\n"
          "    @(posedge clk) (te1, q = '{5, 6, 7}) ##1"
          " (te2 && q.size() == 3);\n"
          "  endproperty\n"
          "  property pa; int aa [int];\n"
          "    @(posedge clk) (te1, aa = '{1: 8}) ##1 (te2 && aa[1] == 8);\n"
          "  endproperty\n"
          "  c1: cover property (pd);\n"
          "  c2: cover property (pq);\n"
          "  c3: cover property (pa);\n"),
      3);
}

TEST(TypedLocals, DISABLED_UnpackedLocalsInAPropertyBodyAreEvaluated) {
  ExpectEachCoverOnce(
      TypedLocalSource(
          "  property pw; int w [2];\n"
          "    @(posedge clk) (te1, w[0] = 3) ##1 (te2 && w[0] == 3);\n"
          "  endproperty\n"
          "  property pb; byte bq [$];\n"
          "    @(posedge clk) (te1, bq = '{9}) ##1 (te2 && bq[0] == 9);\n"
          "  endproperty\n"
          "  c1: cover property (pw);\n"
          "  c2: cover property (pb);\n"),
      2);
}

TEST(TypedLocals, DISABLED_UnpackedLocalsInASequenceBodyKeepItsClock) {
  ExpectEachCoverOnce(
      TypedLocalSource(
          "  sequence sw; int w [2];\n"
          "    @(posedge clk) (te1, w[0] = 3) ##1 (te2 && w[0] == 3);\n"
          "  endsequence\n"
          "  sequence sb; byte bq [$];\n"
          "    @(posedge clk) (te1, bq = '{9}) ##1 (te2 && bq[0] == 9);\n"
          "  endsequence\n"
          "  c1: cover property (sw);\n"
          "  c2: cover property (sb);\n"),
      2);
}

}  // namespace
