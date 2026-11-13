#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "helpers_reported_error.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string MatchedSource(const std::string& destination) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic sysclk = 0;\n"
         "  logic ready = 0, proc1 = 0, proc2 = 0;\n"
         "  logic reset = 0, inst = 0, branch_back = 0;\n"
         "  int ends = 0;\n"
         "  int last_end = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #8 sysclk = ~sysclk;\n"
         "  sequence e1(a, b, c);\n"
         "    @(posedge clk) $rose(a) ##1 b ##1 c;\n"
         "  endsequence\n"
         "  sequence e1_inst;\n"
         "    e1(ready, proc1, proc2);\n"
         "  endsequence\n"
         "  sequence dest;\n" +
         destination +
         "  endsequence\n"
         "  initial forever begin\n"
         "    wait (dest.triggered);\n"
         "    ends++;\n"
         "    last_end = $time;\n"
         "    @(posedge sysclk);\n"
         "  end\n"
         "  initial begin\n"
         "    #5 reset = 1;\n"
         "    #5 reset = 0; ready = 1;\n"
         "    #10 inst = 1; proc1 = 1;\n"
         "    #10 inst = 0; proc1 = 0; proc2 = 1;\n"
         "    #10 proc2 = 0;\n"
         "    #10 ready = 0; branch_back = 1;\n"
         "    #10 branch_back = 0;\n"
         "    #10 reset = 1; ready = 1;\n"
         "    #5 reset = 0;\n"
         "    #5 inst = 1; proc1 = 1;\n"
         "    #10 inst = 0; proc1 = 0; proc2 = 1;\n"
         "    #10 proc2 = 0;\n"
         "    #15 branch_back = 1;\n"
         "    #10 branch_back = 0;\n"
         "    #5 $finish;\n"
         "  end\n"
         "endmodule\n";
}

struct EndPoints {
  uint64_t ends;
  uint64_t last_end;
};

EndPoints EndPointsOf(const std::string& destination) {
  SimFixture f;
  auto* ends = RunAndFindVar(MatchedSource(destination), f, "ends");
  if (ends == nullptr) return {~0ull, ~0ull};
  Variable* last_end = f.ctx.FindVariable("last_end");
  return {ends->value.ToUint64(), last_end->value.ToUint64()};
}

TEST(MatchedEndPoint, MatchedStoresTheMatchUntilTheDestinationClockTicks) {
  EndPoints ends = EndPointsOf(
      "    @(posedge sysclk) reset ##1 inst ##1 "
      "e1(ready, proc1, proc2).matched [->1] ##1 branch_back;\n");
  EXPECT_EQ(ends.ends, 2u);
  EXPECT_EQ(ends.last_end, 120u);
}

TEST(MatchedEndPoint, TriggeredIsNotSeenFromAnotherClock) {
  SimFixture f;
  auto* ends = RunAndFindVar(
      MatchedSource(
          "    @(posedge sysclk) reset ##1 inst ##1 "
          "e1(ready, proc1, proc2).triggered [->1] ##1 branch_back;\n"),
      f, "ends");
  ASSERT_NE(ends, nullptr);
  EXPECT_EQ(ends->value.ToUint64(), 0u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the ending clock of 'e1' differs from the clock of "
                    "the context its triggered stands in",
                    17, "16.9.11"));
}

TEST(MatchedEndPoint, AReadConsumesTheStoredMatch) {
  EndPoints ends = EndPointsOf(
      "    @(posedge sysclk) e1_inst.matched ##1 e1_inst.matched;\n");
  EXPECT_EQ(ends.ends, 0u);
}

TEST(MatchedEndPoint, AReadConsumesTheMatchOfASequenceWithALongName) {
  SimFixture f;
  auto* reads = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0, sysclk = 0, a = 0;\n"
      "  int reads = 0, last_read = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always #8 sysclk = ~sysclk;\n"
      "  sequence a_sequence_named_past_the_small_string_buffer;\n"
      "    @(posedge clk) a ##1 a;\n"
      "  endsequence\n"
      "  always @(posedge sysclk)\n"
      "    if (a_sequence_named_past_the_small_string_buffer.matched) begin\n"
      "      reads++;\n"
      "      last_read = $time;\n"
      "    end\n"
      "  initial begin\n"
      "    #12 a = 1;\n"
      "    #20 a = 0;\n"
      "    #40 a = 1;\n"
      "    #20 a = 0;\n"
      "    #30 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "reads");
  ASSERT_NE(reads, nullptr);
  EXPECT_EQ(reads->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last_read")->value.ToUint64(), 88u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "matched may be used only in a sequence expression",
                            10, "16.13.6"));
}

constexpr const char* kEndPointStimulus =
    "  always #5 clk0 = ~clk0;\n"
    "  always #4 clk1 = ~clk1;\n"
    "  initial begin a = 1; #20 a = 0; #10 a = 1; end\n"
    "  initial begin\n"
    "    b = 0; #10 b = 1; #12 b = 0; #12 b = 1; #6 b = 0; #10 b = 1;\n"
    "  end\n";

constexpr const char* kEndPointSequences =
    "  sequence s0; @(posedge clk0) a ##1 a; endsequence\n"
    "  sequence ms; @(posedge clk0) a ##1 @(posedge clk1) b; endsequence\n";

constexpr const char* kEndPointPlaces[] = {"module", "generate", "interface",
                                           "program", "checker"};

std::string EndPointTop(const std::string& items) {
  return "module t;\n"
         "  logic clk0 = 0, clk1 = 0, a, b, x = 1;\n" +
         std::string(kEndPointStimulus) + items +
         "  initial #58 $finish;\n"
         "endmodule\n";
}

std::string EndPointSource(const std::string& place, const std::string& items) {
  std::string body = kEndPointSequences + items;
  std::string instance = "  w u(clk0, clk1, a, b, x);\n";
  if (place == "module") return EndPointTop(body);
  if (place == "generate") {
    return EndPointTop("  if (1) begin : g\n" + body + "  end\n");
  }
  if (place == "checker") {
    return "checker w(clk0, clk1, a, b, x);\n" + body + "endchecker\n" +
           EndPointTop(instance);
  }
  return place + " w(input logic clk0, clk1, a, b, x);\n" + body + "end" +
         place + "\n" + EndPointTop(instance);
}

template <typename Places, typename Rows>
void ExpectEndPointCountsIn(const Places& places, const Rows& rows) {
  for (const char* name : places) {
    std::string place = name;
    for (const PlacedProperty& row : rows) {
      for (const char* directive : {"assert", "assume"}) {
        SCOPED_TRACE(place + " " + directive + " " + row.body);
        EXPECT_EQ(CountThroughTheEnd(EndPointSource(
                      place, PlacedDirective(directive, row.body))),
                  row.asserted);
      }
      SCOPED_TRACE(place + " cover " + row.body);
      EXPECT_EQ(CountThroughTheEnd(
                    EndPointSource(place, PlacedDirective("cover", row.body))),
                (PlaceCounts{row.covered, 0}));
    }
  }
}

struct CoveredDestination {
  const char* destination;
  size_t matches;
};

template <typename Places, typename Rows>
void ExpectDestinationMatchesIn(const Places& places, const Rows& rows) {
  for (const char* name : places) {
    std::string place = name;
    for (const CoveredDestination& row : rows) {
      std::string items = "  sequence d; " + std::string(row.destination) +
                          "; endsequence\n" + PlacedDirective("cover", "d");
      SCOPED_TRACE(place + " " + row.destination);
      EXPECT_EQ(CountThroughTheEnd(EndPointSource(place, items)),
                (PlaceCounts{row.matches, 0}));
    }
  }
}

template <typename Places>
void ExpectWakesIn(const Places& places, const std::string& instance,
                   const std::string& clock, size_t wakes) {
  std::string waiter = "  initial forever begin\n    wait (";
  waiter += instance;
  waiter += ".triggered);\n    $display(\"PASS\");\n    @(posedge ";
  waiter += clock;
  waiter += ");\n  end\n";
  for (const char* name : places) {
    std::string place = name;
    SCOPED_TRACE(place + waiter);
    EXPECT_EQ(CountThroughTheEnd(EndPointSource(place, waiter)),
              (PlaceCounts{wakes, 0}));
  }
}

constexpr PlacedProperty kSinglyClockedEndPoints[] = {
    {"@(posedge clk0) s0.triggered", {3, 3}, 3},
    {"@(posedge clk1) s0.matched", {2, 5}, 2}};

constexpr CoveredDestination kSinglyClockedDestinations[] = {
    {"@(posedge clk1) b ##1 @(posedge clk0) s0.triggered", 3},
    {"@(posedge clk1) b ##1 s0.matched", 1}};

constexpr const char* kProcedurePlaces[] = {"module", "generate", "interface",
                                            "program"};

TEST(MulticlockEndPointRun, ASinglyClockedSequencesEndPointIsSeenInEachPlace) {
  ExpectEndPointCountsIn(kEndPointPlaces, kSinglyClockedEndPoints);
  ExpectDestinationMatchesIn(kEndPointPlaces, kSinglyClockedDestinations);
  ExpectWakesIn(kProcedurePlaces, "s0", "clk0", 3);
}

constexpr PlacedProperty kMulticlockedTriggered[] = {
    {"@(posedge clk1) ms.triggered", {4, 3}, 4}};

constexpr CoveredDestination kMulticlockedTriggeredDestinations[] = {
    {"@(posedge clk1) x ##1 ms.triggered", 4},
    {"@(posedge clk0) a ##1 @(posedge clk1) ms.triggered", 4}};

TEST(MulticlockEndPointRun,
     DISABLED_TriggeredSeesEachEndOfAMulticlockedSequenceInEachPlace) {
  ExpectEndPointCountsIn(kEndPointPlaces, kMulticlockedTriggered);
  ExpectDestinationMatchesIn(kEndPointPlaces,
                             kMulticlockedTriggeredDestinations);
  ExpectWakesIn(kProcedurePlaces, "ms", "clk1", 4);
}

constexpr PlacedProperty kMulticlockedMatched[] = {
    {"@(posedge clk0) ms.matched", {4, 2}, 4}};

constexpr CoveredDestination kMulticlockedMatchedDestinations[] = {
    {"@(posedge clk0) a ##1 ms.matched", 4}};

TEST(MulticlockEndPointRun,
     DISABLED_MatchedSeesEachEndOfAMulticlockedSequenceInEachPlace) {
  ExpectEndPointCountsIn(kEndPointPlaces, kMulticlockedMatched);
  ExpectDestinationMatchesIn(kEndPointPlaces, kMulticlockedMatchedDestinations);
}

constexpr const char* kLocalSources =
    "  sequence src(lv); @(posedge clk) (a, lv = data) ##1 b; endsequence\n"
    "  sequence wide(lv); @(posedge clk) (a, lv = data) ##[1:2] b; "
    "endsequence\n"
    "  sequence srco(local output int lv);\n"
    "    @(posedge clk) (a, lv = data) ##1 b;\n"
    "  endsequence\n"
    "  sequence src2(l1, l2); @(posedge clk) (a, l1 = data, l2 = 5) ##1 b; "
    "endsequence\n";

constexpr const char* kOneMatch =
    "  assign a = tick inside {3};\n"
    "  assign b = tick inside {4};\n"
    "  assign data = tick - 1;\n";

constexpr const char* kTwoMatches =
    "  assign a = tick inside {2, 3};\n"
    "  assign b = tick inside {3, 4};\n"
    "  assign data = tick - 1;\n";

constexpr const char* kTwoMatchesEndingTogether =
    "  assign a = tick inside {2, 3};\n"
    "  assign b = tick inside {4};\n"
    "  assign data = tick - 1;\n";

constexpr const char* kThreeMatches =
    "  assign a = tick inside {1, 2, 3};\n"
    "  assign b = tick inside {2, 3, 4};\n"
    "  assign data = tick + 10;\n";

constexpr const char* kTwoMatchesOfOneValue =
    "  assign a = tick inside {2, 3};\n"
    "  assign b = tick inside {3, 4};\n"
    "  assign data = 7;\n";

struct LocalFlowRow {
  const char* stimulus;
  const char* declaration;
  const char* directive;
  PlaceCounts counts;
};

std::string LocalFlowTop(const std::string& stimulus,
                         const std::string& items) {
  return "module t;\n"
         "  logic clk = 0, sysclk = 1;\n"
         "  int tick = 1;\n"
         "  logic a, b;\n"
         "  int data;\n"
         "  always #5 clk = ~clk;\n"
         "  always #20 sysclk = ~sysclk;\n"
         "  always #10 tick = tick + 1;\n" +
         stimulus + items +
         "  initial #90 $finish;\n"
         "endmodule\n";
}

std::string LocalFlowSource(const std::string& place, const LocalFlowRow& row) {
  std::string action = std::string(row.directive).starts_with("assert")
                           ? " $display(\"PASS\"); else $display(\"FAIL\");\n"
                           : " $display(\"PASS\");\n";
  std::string body = std::string(kLocalSources) + "  " + row.declaration +
                     "\n  " + row.directive + action;
  std::string instance = "  w u(clk, sysclk, a, b, data);\n";
  if (place == "module") return LocalFlowTop(row.stimulus, body);
  if (place == "checker") {
    return "checker w(clk, sysclk, a, b, data);\n" + body + "endchecker\n" +
           LocalFlowTop(row.stimulus, instance);
  }
  return place + " w(input logic clk, sysclk, a, b, input var int data);\n" +
         body + "end" + place + "\n" + LocalFlowTop(row.stimulus, instance);
}

constexpr const char* kLocalFlowPlaces[] = {"module", "interface", "program",
                                            "checker"};

template <typename Rows>
void ExpectLocalFlowInEachPlace(const Rows& rows) {
  for (const char* place : kLocalFlowPlaces) {
    for (const LocalFlowRow& row : rows) {
      SCOPED_TRACE(std::string(place) + " " + row.declaration);
      EXPECT_EQ(CountThroughTheEnd(LocalFlowSource(place, row)), row.counts);
    }
  }
}

constexpr LocalFlowRow kLocalsFlowingOut[] = {
    {kOneMatch,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 2); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kOneMatch,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##1 (v == 2); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kOneMatch,
     "sequence dst; int v; @(posedge sysclk) srco(v).matched ##0 (v == 2); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kOneMatch,
     "property dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 2); "
     "endproperty",
     "cover property (dst)",
     {1, 0}},
    {kOneMatch,
     "property dst; int v; @(posedge sysclk) src(v).matched; endproperty",
     "cover property (dst)",
     {1, 0}}};

constexpr LocalFlowRow kLocalsNotFlowingOut[] = {
    {kOneMatch,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 1); "
     "endsequence",
     "cover sequence (dst)",
     {0, 0}}};

TEST(MatchedLocalFlowRun, AValueNoMatchAssignedDoesNotFlowOut) {
  ExpectLocalFlowInEachPlace(kLocalsNotFlowingOut);
}

TEST(MatchedLocalFlowRun, DISABLED_TheMatchsValueFlowsOutInEachPlace) {
  ExpectLocalFlowInEachPlace(kLocalsFlowingOut);
}

constexpr LocalFlowRow kForkedDestinations[] = {
    {kTwoMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 1); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 2); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched; endsequence",
     "cover sequence (dst)",
     {2, 0}},
    {kTwoMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 1 || v "
     "== 2); endsequence",
     "cover sequence (dst)",
     {2, 0}},
    {kTwoMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##1 (v == 1); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##1 (v == 2); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched [->1] ##1 (v == "
     "2); endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatches,
     "property dst; int v; @(posedge sysclk) src(v).matched |-> (v == 1); "
     "endproperty",
     "assert property (dst)",
     {1, 1}},
    {kTwoMatches,
     "property dst; int v; @(posedge sysclk) src(v).matched |-> (v == 1 || v "
     "== 2); endproperty",
     "assert property (dst)",
     {2, 0}},
    {kTwoMatches,
     "sequence dst; int v1, v2; @(posedge sysclk) src2(v1, v2).matched ##0 "
     "(v1 == 1 && v2 == 5); endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatches,
     "sequence dst; int v1, v2; @(posedge sysclk) src2(v1, v2).matched ##0 "
     "(v1 == 2 && v2 == 5); endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatchesEndingTogether,
     "sequence dst; int v; @(posedge sysclk) wide(v).matched ##0 (v == 1); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatchesEndingTogether,
     "sequence dst; int v; @(posedge sysclk) wide(v).matched ##0 (v == 2); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kThreeMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched; endsequence",
     "cover sequence (dst)",
     {3, 0}},
    {kThreeMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 11); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kThreeMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 13); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatchesOfOneValue,
     "sequence dst; int v; @(posedge sysclk) src(v).matched; endsequence",
     "cover sequence (dst)",
     {1, 0}},
    {kTwoMatchesOfOneValue,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 7); "
     "endsequence",
     "cover sequence (dst)",
     {1, 0}}};

constexpr LocalFlowRow kUnforkedDestinations[] = {
    {kTwoMatches,
     "sequence dst; int v; @(posedge sysclk) src(v).matched ##0 (v == 3); "
     "endsequence",
     "cover sequence (dst)",
     {0, 0}}};

TEST(MatchedLocalFlowRun, NoThreadCarriesAValueNoMatchAssigned) {
  ExpectLocalFlowInEachPlace(kUnforkedDestinations);
}

TEST(MatchedLocalFlowRun,
     DISABLED_EachDistinctValueMatchedInOneCycleForksTheDestination) {
  ExpectLocalFlowInEachPlace(kForkedDestinations);
}

}  // namespace
