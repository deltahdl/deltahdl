#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string ClockFlowSource(const std::string& items) {
  return "module t;\n"
         "  logic clk0 = 0;\n"
         "  logic clk1 = 0;\n"
         "  int tick = 1;\n"
         "  logic x, y, z, w, x2, y2, z2, v, w3, x3, y3, z3, xi, yd, zi, xj;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int fail_sum = 0;\n"
         "  always #5 clk0 = ~clk0;\n"
         "  always #10 tick = tick + 1;\n"
         "  initial begin\n"
         "    #12 clk1 = 1; #8 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #10 clk1 = 1; #5 clk1 = 0; #7 clk1 = 1; #8 clk1 = 0;\n"
         "    #7 clk1 = 1; #6 clk1 = 0;\n"
         "  end\n"
         "  assign x = tick inside {1, 4};\n"
         "  assign y = tick inside {2, 5};\n"
         "  assign z = tick inside {3};\n"
         "  assign w = tick inside {1};\n"
         "  assign x2 = tick inside {2};\n"
         "  assign y2 = tick inside {3};\n"
         "  assign z2 = tick inside {4};\n"
         "  assign v = tick inside {5};\n"
         "  assign w3 = tick inside {6};\n"
         "  assign x3 = tick inside {6};\n"
         "  assign y3 = tick inside {6};\n"
         "  assign z3 = tick inside {7};\n"
         "  assign xi = tick inside {1};\n"
         "  assign yd = tick inside {2};\n"
         "  assign zi = tick inside {2};\n"
         "  assign xj = tick inside {1, 4};\n"
         "  sequence s_d;\n"
         "    @(posedge clk1) yd;\n"
         "  endsequence\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

struct FlowCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t fail_sum;
};

FlowCounts CountsOfFlow(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ClockFlowSource("  p: assert property (" + spec +
                      ") passes++; else begin fails++; fail_sum += $time; "
                      "end\n"),
      f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* fail_sum = f.ctx.FindVariable("fail_sum");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          fail_sum->value.ToUint64()};
}

TEST(ClockFlow, TheClockFlowsAcrossTheImplication) {
  FlowCounts written = CountsOfFlow(
      "@(posedge clk0) x |=> @(posedge clk0) y ##1 @(posedge clk1) z");
  EXPECT_EQ(written.passes, 7u);
  EXPECT_EQ(written.fails, 1u);
  EXPECT_EQ(written.fail_sum, 57u);
  FlowCounts implied =
      CountsOfFlow("@(posedge clk0) x |=> y ##1 @(posedge clk1) z");
  EXPECT_EQ(implied.passes, 7u);
  EXPECT_EQ(implied.fails, 1u);
  EXPECT_EQ(implied.fail_sum, 57u);
}

TEST(ClockFlow, ConcatenationAndImplicationAreAdjoint) {
  FlowCounts concat =
      CountsOfFlow("@(posedge clk0) x ##1 y |=> @(posedge clk1) z");
  EXPECT_EQ(concat.passes, 7u);
  EXPECT_EQ(concat.fails, 1u);
  EXPECT_EQ(concat.fail_sum, 57u);
  FlowCounts nested =
      CountsOfFlow("@(posedge clk0) x |=> y |=> @(posedge clk1) z");
  EXPECT_EQ(nested.passes, 7u);
  EXPECT_EQ(nested.fails, 1u);
  EXPECT_EQ(nested.fail_sum, 57u);
}

TEST(ClockFlow, AClockInParenthesesFlowsNoFurther) {
  FlowCounts counts =
      CountsOfFlow("@(posedge clk0) w ##1 (x2 ##1 @(posedge clk1) y2) |=> z2");
  EXPECT_EQ(counts.passes, 8u);
  EXPECT_EQ(counts.fails, 0u);
}

TEST(ClockFlow, TheClockDistributesToTheOperandsOfAnAnd) {
  FlowCounts counts = CountsOfFlow(
      "@(posedge clk0) v |=> (w3 ##1 @(posedge clk1) x3) and (y3 ##1 z3)");
  EXPECT_EQ(counts.passes, 8u);
  EXPECT_EQ(counts.fails, 0u);
}

TEST(ClockFlow, AClockInAnInstanceFlowsNoFurther) {
  FlowCounts counts = CountsOfFlow("@(posedge clk0) xi |=> s_d ##1 zi");
  EXPECT_EQ(counts.passes, 8u);
  EXPECT_EQ(counts.fails, 0u);
}

TEST(ClockFlow, TheSecondOfTwoClocksJuxtaposedNullifiesTheFirst) {
  FlowCounts counts = CountsOfFlow("@(posedge clk1) @(posedge clk0) xj");
  EXPECT_EQ(counts.passes, 2u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.fail_sum, 280u);
}

struct FlowRow {
  size_t stimulus;
  const char* flowed;
  const char* clocked;
  const char* contrast;
};

constexpr const char* kFlowClocks =
    "  int n = 0;\n"
    "  always #1 n = n + 1;\n"
    "  initial d = 0;\n"
    "  always #2 d = ~d;\n";

constexpr const char* kFlowDeclarations =
    "  sequence sq; c ##1 a; endsequence\n"
    "  sequence sqe; @(posedge d) c ##1 a; endsequence\n"
    "  sequence sqp; @(posedge clk) c ##1 a; endsequence\n"
    "  property pr; c |=> a; endproperty\n"
    "  sequence s_d; @(posedge d) b; endsequence\n"
    "  sequence sj; @(posedge clk) @(posedge d) a ##1 b; endsequence\n"
    "  sequence sje; @(posedge d) a ##1 b; endsequence\n"
    "  sequence sjp; @(posedge clk) a ##1 b; endsequence\n";

constexpr const char* kFlowStimuli[] = {
    "  assign a = n[0] ^ n[3];\n"
    "  assign b = n[0] ^ n[1];\n"
    "  assign c = n[1] | n[0];\n",
    "  assign a = n[4] ^ n[0];\n"
    "  assign b = n[4] & n[3];\n"
    "  assign c = n[3] ^ n[4];\n",
    "  assign a = n[3] | n[4];\n"
    "  assign b = n[1] ^ n[4];\n"
    "  assign c = n[1] & n[2];\n",
    "  assign a = n[0] | n[5];\n"
    "  assign b = n[4] | n[0];\n"
    "  assign c = n[3] ^ n[0];\n",
    "  assign a = n[3] | n[2];\n"
    "  assign b = n[1] | n[3];\n"
    "  assign c = n[3] | n[1];\n",
    "  assign a = n[3] | n[2];\n"
    "  assign b = n[3] ^ n[4];\n"
    "  assign c = n[0] & n[2];\n",
};

constexpr FlowRow kFlowAcrossOperators[] = {
    {3, "a ##1 @(posedge d) b |-> s_always [0:1] (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge d) s_always [0:1] (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge clk) s_always [0:1] (c ##1 a)"},
    {2, "a ##1 @(posedge d) b |=> (nexttime c) or (nexttime a)",
     "a ##1 @(posedge d) b |=> @(posedge d) (nexttime c) or (nexttime a)",
     "a ##1 @(posedge d) b |=> @(posedge clk) (nexttime c) or (nexttime a)"},
    {1, "a ##1 @(posedge d) b |=> c until a",
     "a ##1 @(posedge d) b |=> @(posedge d) c until a",
     "a ##1 @(posedge d) b |=> @(posedge clk) c until a"},
    {1, "a ##1 @(posedge d) b |=> c s_until a",
     "a ##1 @(posedge d) b |=> @(posedge d) c s_until a",
     "a ##1 @(posedge d) b |=> @(posedge clk) c s_until a"},
    {1, "a ##1 @(posedge d) b |=> c until_with a",
     "a ##1 @(posedge d) b |=> @(posedge d) c until_with a",
     "a ##1 @(posedge d) b |=> @(posedge clk) c until_with a"},
    {1, "a ##1 @(posedge d) b |=> c s_until_with a",
     "a ##1 @(posedge d) b |=> @(posedge d) c s_until_with a",
     "a ##1 @(posedge d) b |=> @(posedge clk) c s_until_with a"}};

constexpr FlowRow kFlowAcrossAnImplication[] = {
    {0, "a |=> @(posedge clk) b ##1 @(posedge d) c",
     "a |=> b ##1 @(posedge d) c", "a |=> b ##1 c"},
    {1, "a ##1 b |=> @(posedge d) c", "a |=> b |=> @(posedge d) c",
     "a |-> b |=> @(posedge d) c"},
    {1, "a ##0 b |=> @(posedge d) c", "a |-> b |=> @(posedge d) c",
     "a |=> b |=> @(posedge d) c"}};

constexpr FlowRow kFlowAroundParentheses[] = {
    {4, "a ##1 (b ##1 @(posedge d) c) |=> a",
     "a ##1 (b ##1 @(posedge d) c) |=> @(posedge clk) a",
     "a ##1 (b ##1 @(posedge d) c) |=> @(posedge d) a"},
    {0, "a |=> (b ##1 @(posedge d) c) and (a ##1 b)",
     "a |=> (b ##1 @(posedge d) c) and (@(posedge clk) a ##1 b)",
     "a |=> (b ##1 @(posedge d) c) and (@(posedge d) a ##1 b)"},
    {0, "a ##1 @(posedge d) b ##1 (c ##1 a) ##1 b",
     "a ##1 @(posedge d) b ##1 (@(posedge d) c ##1 a) ##1 @(posedge d) b",
     "a ##1 @(posedge d) b ##1 (@(posedge clk) c ##1 a) ##1 b"}};

constexpr FlowRow kFlowAroundInstances[] = {
    {0, "a ##1 @(posedge d) b |=> pr",
     "a ##1 @(posedge d) b |=> @(posedge d) pr",
     "a ##1 @(posedge d) b |=> @(posedge clk) pr"},
    {0, "a |=> s_d ##1 c", "a |=> s_d ##1 @(posedge clk) c",
     "a |=> s_d ##1 @(posedge d) c"},
    {0, "a ##1 @(posedge d) b ##1 sq ##1 b",
     "a ##1 @(posedge d) b ##1 sqe ##1 @(posedge d) b",
     "a ##1 @(posedge d) b ##1 sqp ##1 b"}};

constexpr FlowRow kJuxtaposedClocks[] = {
    {0, "a |=> @(posedge clk) @(posedge d) b ##1 c",
     "a |=> @(posedge d) b ##1 c", "a |=> b ##1 c"},
    {0, "a ##1 @(posedge clk) @(posedge d) b ##1 c",
     "a ##1 @(posedge d) b ##1 c", "a ##1 b ##1 c"},
    {0, "sj", "sje", "sjp"}};

constexpr FlowRow kConsequentsAfterAClockChange[] = {
    {0, "a ##1 @(posedge d) b |=> c ##1 c ##1 a",
     "a ##1 @(posedge d) b |=> @(posedge d) (c ##1 c ##1 a)",
     "a ##1 @(posedge d) b |=> @(posedge clk) (c ##1 c ##1 a)"},
    {0, "a ##1 @(posedge d) b |-> ##1 c ##1 c ##1 a",
     "a ##1 @(posedge d) b |-> @(posedge d) (##1 c ##1 c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge clk) (##1 c ##1 c ##1 a)"},
    {0, "a ##1 @(posedge d) b |=> c[*2] ##1 a",
     "a ##1 @(posedge d) b |=> @(posedge d) (c[*2] ##1 a)",
     "a ##1 @(posedge d) b |=> @(posedge clk) (c[*2] ##1 a)"},
    {0, "a ##1 @(posedge d) b |=> not (c ##1 a)",
     "a ##1 @(posedge d) b |=> @(posedge d) not (c ##1 a)",
     "a ##1 @(posedge d) b |=> @(posedge clk) not (c ##1 a)"},
    {0, "a ##1 @(posedge d) b #-# c ##1 a",
     "a ##1 @(posedge d) b #-# @(posedge d) (c ##1 a)",
     "a ##1 @(posedge d) b #-# @(posedge clk) (c ##1 a)"},
    {0, "a ##1 @(posedge d) b #=# c ##1 a",
     "a ##1 @(posedge d) b #=# @(posedge d) (c ##1 a)",
     "a ##1 @(posedge d) b #=# @(posedge clk) (c ##1 a)"},
    {0, "a ##1 @(posedge d) b |-> nexttime (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge d) nexttime (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge clk) nexttime (c ##1 a)"},
    {0, "a ##1 @(posedge d) b |-> s_nexttime (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge d) s_nexttime (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge clk) s_nexttime (c ##1 a)"},
    {0, "a ##1 @(posedge d) b |-> always [0:1] (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge d) always [0:1] (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge clk) always [0:1] (c ##1 a)"},
    {0, "a ##1 @(posedge d) b |-> eventually [1:2] (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge d) eventually [1:2] (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge clk) eventually [1:2] (c ##1 a)"},
    {0, "a ##1 @(posedge d) b |-> s_eventually [1:2] (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge d) s_eventually [1:2] (c ##1 a)",
     "a ##1 @(posedge d) b |-> @(posedge clk) s_eventually [1:2] (c ##1 a)"},
    {0, "a ##1 @(posedge d) b |=> (c ##1 a) or (a ##1 c)",
     "a ##1 @(posedge d) b |=> @(posedge d) ((c ##1 a) or (a ##1 c))",
     "a ##1 @(posedge d) b |=> @(posedge clk) ((c ##1 a) or (a ##1 c))"},
    {0, "a ##1 @(posedge d) b |=> (c ##1 a) and (b ##2 c)",
     "a ##1 @(posedge d) b |=> @(posedge d) ((c ##1 a) and (b ##2 c))",
     "a ##1 @(posedge d) b |=> @(posedge clk) ((c ##1 a) and (b ##2 c))"},
    {0, "a ##1 @(posedge d) b |=> (c ##1 a) intersect (b ##1 c)",
     "a ##1 @(posedge d) b |=> @(posedge d) ((c ##1 a) intersect (b ##1 c))",
     "a ##1 @(posedge d) b |=> @(posedge clk) ((c ##1 a) intersect (b ##1 c))"},
    {0, "a ##1 @(posedge d) b |=> (c |=> a) and (b |=> c)",
     "a ##1 @(posedge d) b |=> @(posedge d) (c |=> a) and (b |=> c)",
     "a ##1 @(posedge d) b |=> @(posedge clk) (c |=> a) and (b |=> c)"},
    {0, "a ##1 @(posedge d) b |=> if (c) (a ##1 b) else (b ##1 a)",
     "a ##1 @(posedge d) b |=> @(posedge d) if (c) (a ##1 b) else (b ##1 a)",
     "a ##1 @(posedge d) b |=> @(posedge clk) if (c) (a ##1 b) else (b ##1 a)"},
    {0, "a ##1 @(posedge d) b |=> sq", "a ##1 @(posedge d) b |=> sqe",
     "a ##1 @(posedge d) b |=> sqp"}};

constexpr FlowRow kMethodsAfterAClockChange[] = {
    {5, "a ##1 @(posedge d) sq.triggered", "a ##1 @(posedge d) sqe.triggered",
     "a ##1 sqp.triggered"},
    {5, "a ##0 @(posedge d) sq.triggered", "a ##0 @(posedge d) sqe.triggered",
     "a ##0 sqp.triggered"},
    {2, "a ##1 @(posedge d) b ##1 sq.matched",
     "a ##1 @(posedge d) b ##1 sqe.matched",
     "a ##1 @(posedge d) b ##1 sqp.matched"},
    {0, "a ##1 @(posedge d) b |-> sq.matched",
     "a ##1 @(posedge d) b |-> sqe.matched",
     "a ##1 @(posedge d) b |-> sqp.matched"},
    {2, "a ##1 @(posedge d) b |=> sq.triggered",
     "a ##1 @(posedge d) b |=> @(posedge d) sqe.triggered",
     "a ##1 @(posedge d) b |=> @(posedge clk) sqp.triggered"},
    {4, "a ##1 @(posedge d) b |=> sq.triggered",
     "a ##1 @(posedge d) b |=> @(posedge d) sqe.triggered",
     "a ##1 @(posedge d) b |=> @(posedge clk) sqp.triggered"}};

constexpr const char* kFlowPlaces[] = {"module",
                                       "generate",
                                       "interface",
                                       "program",
                                       "checker",
                                       "module property",
                                       "interface property",
                                       "checker property",
                                       "clocked procedural"};

std::string FlowSource(const std::string& place, const std::string& directive,
                       size_t stimulus, const std::string& body) {
  bool outside = place == "package property" || place == "unit";
  return ClockedPlaceSource(place, directive, body,
                            std::string(kFlowClocks) + kFlowStimuli[stimulus],
                            outside ? "" : kFlowDeclarations);
}

template <typename Places, typename Rows>
void ExpectFlowedAsClockedIn(const Places& places, const Rows& rows) {
  for (const char* name : places) {
    std::string place = name;
    for (const FlowRow& row : rows) {
      for (const char* directive : {"assert", "assume", "cover"}) {
        SCOPED_TRACE(place + " " + directive + " " + row.flowed);
        EXPECT_EQ(CountThroughTheEnd(
                      FlowSource(place, directive, row.stimulus, row.flowed)),
                  CountThroughTheEnd(
                      FlowSource(place, directive, row.stimulus, row.clocked)));
      }
    }
  }
}

template <typename Rows>
void ExpectFlowedAsClockedInEachPlace(const Rows& rows) {
  ExpectFlowedAsClockedIn(kFlowPlaces, rows);
  ExpectFlowedAsClockedIn(kDefaultClockedPlaces, rows);
}

template <typename Rows>
void ExpectTheTwoClocksToDiffer(const Rows& rows) {
  for (const FlowRow& row : rows) {
    SCOPED_TRACE(row.clocked);
    bool differ = false;
    for (const char* directive : {"assert", "cover"}) {
      differ =
          differ || CountThroughTheEnd(FlowSource("module", directive,
                                                  row.stimulus, row.clocked)) !=
                        CountThroughTheEnd(FlowSource(
                            "module", directive, row.stimulus, row.contrast));
    }
    EXPECT_TRUE(differ);
  }
}

TEST(ClockFlowRun, EachRowsTwoClocksGiveDifferentCounts) {
  ExpectTheTwoClocksToDiffer(kFlowAcrossOperators);
  ExpectTheTwoClocksToDiffer(kFlowAcrossAnImplication);
  ExpectTheTwoClocksToDiffer(kFlowAroundParentheses);
  ExpectTheTwoClocksToDiffer(kFlowAroundInstances);
  ExpectTheTwoClocksToDiffer(kJuxtaposedClocks);
  ExpectTheTwoClocksToDiffer(kConsequentsAfterAClockChange);
  ExpectTheTwoClocksToDiffer(kMethodsAfterAClockChange);
}

TEST(ClockFlowRun, AChangedClockFlowsAcrossEachOperatorInEachPlace) {
  ExpectFlowedAsClockedInEachPlace(kFlowAcrossOperators);
}

TEST(ClockFlowRun, AClockFlowsAcrossAnImplicationAsTheEquivalencesSay) {
  ExpectFlowedAsClockedInEachPlace(kFlowAcrossAnImplication);
}

TEST(ClockFlowRun, AClockFlowsIntoParenthesesButNotOutOfThem) {
  ExpectFlowedAsClockedInEachPlace(kFlowAroundParentheses);
}

TEST(ClockFlowRun, AClockFlowsIntoAnInstanceButNotOutOfIt) {
  ExpectFlowedAsClockedInEachPlace(kFlowAroundInstances);
}

TEST(ClockFlowRun, TheSecondOfTwoJuxtaposedClocksIsInForce) {
  ExpectFlowedAsClockedIn(kFlowPlaces, kJuxtaposedClocks);
}

TEST(ClockFlowRun,
     DISABLED_ADeclaredJuxtapositionUnderDefaultClockingStartsOnTheSecond) {
  ExpectFlowedAsClockedIn(kDefaultClockedPlaces, kJuxtaposedClocks);
}

TEST(ClockFlowRun, DISABLED_AConsequentAfterAClockChangeRunsOnTheNewClock) {
  ExpectFlowedAsClockedInEachPlace(kConsequentsAfterAClockChange);
}

TEST(ClockFlowRun,
     DISABLED_AnUnclockedSequenceUnderAMethodTakesTheChangedClock) {
  ExpectFlowedAsClockedInEachPlace(kMethodsAfterAClockChange);
}

template <typename Places>
void ExpectEveryUndeclaredRowIn(const Places& places) {
  ExpectFlowedAsClockedIn(places, kFlowAcrossOperators);
  ExpectFlowedAsClockedIn(places, kFlowAcrossAnImplication);
  ExpectFlowedAsClockedIn(places, kFlowAroundParentheses);
  ExpectFlowedAsClockedIn(places,
                          std::initializer_list<FlowRow>{kJuxtaposedClocks[0],
                                                         kJuxtaposedClocks[1]});
}

TEST(ClockFlowRun, DISABLED_AClockFlowsInAPackageProperty) {
  ExpectEveryUndeclaredRowIn(
      std::initializer_list<const char*>{"package property"});
}

TEST(ClockFlowRun, DISABLED_AClockFlowsInACompilationUnitProperty) {
  ExpectEveryUndeclaredRowIn(std::initializer_list<const char*>{"unit"});
}

}  // namespace
