#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

std::string InferenceRunSource(const std::string& procedure) {
  std::string shown = procedure;
  size_t at = shown.find("x1: assert property (");
  size_t close = shown.find(");", at);
  shown.replace(close, 2, ") else $display(\"x1 %0t\", $time);");
  return "module t;\n"
         "  logic clk = 0, clk2 = 0, a = 0, b = 1, q, d = 0;\n"
         "  event ev;\n"
         "  clocking cb @(posedge clk); input b; output d; endclocking\n"
         "  default clocking dc @(posedge clk2); endclocking\n"
         "  always #5 clk = ~clk;\n"
         "  always #7 clk2 = ~clk2;\n"
         "  always #10 -> ev;\n"
         "  initial #28 $finish;\n"
         "  " +
         shown +
         "\n"
         "endmodule\n";
}

struct InferenceRunRow {
  const char* procedure;
  const char* failures;
};

void ExpectFailuresAt(const InferenceRunRow& row) {
  SCOPED_TRACE(row.procedure);
  SimFixture f;
  std::string out = RunCapture(InferenceRunSource(row.procedure), f);
  EXPECT_EQ(out, std::string(row.failures) + "$finish at time 28\n");
}

constexpr InferenceRunRow kInferredRuns[] = {
    {"always @(posedge clk) begin q <= #1 d; x1: assert property (a); end",
     "x1 5\nx1 15\nx1 25\n"},
    {"initial begin @(posedge clk); x1: assert property (a); end", "x1 5\n"},
    {"always @(edge clk) begin x1: assert property (a); end",
     "x1 5\nx1 10\nx1 15\nx1 20\nx1 25\n"},
    {"always @(posedge (clk & b)) begin x1: assert property (a); end",
     "x1 5\nx1 15\nx1 25\n"},
    {"always @(ev) begin x1: assert property (a); end", "x1 10\nx1 20\n"},
    {"always @(cb) begin x1: assert property (a); end", "x1 5\nx1 15\nx1 25\n"},
    {"always @(ev or posedge clk2) begin q = clk2; "
     "x1: assert property (a); end",
     "x1 10\nx1 10\nx1 20\n"},
    {"always @(posedge clk iff b) begin q = b; x1: assert property (a); end",
     "x1 5\nx1 15\nx1 25\n"},
    {"always @(posedge clk) begin assert (clk); x1: assert property (clk); end",
     "x1 5\nx1 15\nx1 25\n"},
    {"always @(posedge clk) begin q <= $rose(a, @(posedge clk)); "
     "x1: assert property (a); end",
     "x1 5\nx1 15\nx1 25\n"},
    {"always @(ev) begin x2: assert property (@(ev) b); "
     "x1: assert property (a); end",
     "x1 10\nx1 20\n"}};

constexpr InferenceRunRow kDefaultRuns[] = {
    {"always @(posedge clk) begin #1; x1: assert property (a); end",
     "x1 7\nx1 21\n"},
    {"initial begin x1: assert property (a); end", "x1 7\n"},
    {"always @(posedge clk or posedge clk2) begin x1: assert property (a); end",
     "x1 7\nx1 7\nx1 21\nx1 21\n"}};

constexpr InferenceRunRow kIntraAssignmentRuns[] = {
    {"always @(posedge clk) begin q = #1 d; x1: assert property (a); end",
     "x1 7\nx1 21\n"},
    {"always @(posedge clk) begin q = @(posedge clk2) d; "
     "x1: assert property (a); end",
     "x1 7\nx1 21\n"},
    {"always @(posedge clk) begin q = repeat (2) @(posedge clk2) d; "
     "x1: assert property (a); end",
     "x1 21\n"},
    {"always @(posedge clk) begin q <= @(posedge clk2) d; "
     "x1: assert property (a); end",
     "x1 7\nx1 21\n"}};

constexpr InferenceRunRow kClockingBlockSignalRuns[] = {
    {"always @(cb) begin q = cb.b; x1: assert property (a); end",
     "x1 5\nx1 15\nx1 25\n"},
    {"always @(cb) begin cb.d <= a; x1: assert property (a); end",
     "x1 5\nx1 15\nx1 25\n"}};

TEST(ProceduralClockInferenceRun,
     EachInferredClockEvaluatesTheAssertionAtItsOwnTicksOverTheDefault) {
  for (const InferenceRunRow& row : kInferredRuns) ExpectFailuresAt(row);
}

TEST(ProceduralClockInferenceRun,
     WhatInfersNoClockIsEvaluatedAtTheDefaultClockingsTicks) {
  for (const InferenceRunRow& row : kDefaultRuns) ExpectFailuresAt(row);
}

TEST(ProceduralClockInferenceRun,
     DISABLED_AnIntraAssignmentTimingControlLeavesTheAssertionToTheDefault) {
  for (const InferenceRunRow& row : kIntraAssignmentRuns) {
    ExpectFailuresAt(row);
  }
}

TEST(ProceduralClockInferenceRun,
     DISABLED_AClockingBlockWhoseSignalTheProcedureUsesClocksTheAssertion) {
  for (const InferenceRunRow& row : kClockingBlockSignalRuns) {
    ExpectFailuresAt(row);
  }
}

constexpr const char* kQueueSignals =
    "  logic clk = 0, fast = 0, slow = 0, a = 1, b = 1;\n"
    "  always #10 clk = ~clk;\n"
    "  always #5 fast = ~fast;\n"
    "  always #20 slow = ~slow;\n"
    "  initial #70 $finish;\n";

std::string QueueStatement(const std::string& directive,
                           const std::string& clock, const std::string& tag) {
  std::string shown = "$display(\"" + tag + " %0t\", $time);";
  if (directive.starts_with("cover")) {
    return directive + " (@(posedge " + clock + ") 1) " + shown;
  }
  return directive + " (@(posedge " + clock + ") 0) else " + shown;
}

std::string QueueSource(const std::string& unit, const std::string& body) {
  std::string procedure = "always @(posedge clk)";
  if (unit == "program") procedure = "initial forever @(posedge clk)";
  if (unit == "checker") procedure = "always_ff @(posedge clk)";
  std::string items = "  " + procedure + " begin\n" + body + "  end\n";
  if (unit == "module") {
    return "module t;\n" + std::string(kQueueSignals) + items + "endmodule\n";
  }
  if (unit == "generate") {
    return "module t;\n" + std::string(kQueueSignals) + "  if (1) begin : g\n" +
           items + "  end\nendmodule\n";
  }
  std::string header = unit == "checker"
                           ? "checker w(clk, fast, slow);\n"
                           : unit + " w(input logic clk, fast, slow);\n";
  return header + items + "end" + unit + "\nmodule t;\n" + kQueueSignals +
         "  w u(clk, fast, slow);\nendmodule\n";
}

constexpr const char* kQueueDirectives[] = {
    "assert property", "assume property", "cover property", "cover sequence"};

constexpr const char* kQueueUnits[] = {"module", "generate", "interface",
                                       "program", "checker"};

constexpr const char* kMaturedAtTheirOwnClocks =
    "f 15\nf 35\nf 55\ns 20\ns 60\ns 60\n";

TEST(ProceduralAssertionQueueRun,
     EachMaturedInstanceWaitsForItsOwnClockForEachKindInEachPlace) {
  for (const char* unit : kQueueUnits) {
    for (const char* directive : kQueueDirectives) {
      SCOPED_TRACE(std::string(unit) + " " + directive);
      std::string body = "    " + QueueStatement(directive, "fast", "f") +
                         "\n    " + QueueStatement(directive, "slow", "s") +
                         "\n";
      SimFixture f;
      std::string out = RunCapture(QueueSource(unit, body), f);
      EXPECT_EQ(PlacedSortedVerdicts(out), kMaturedAtTheirOwnClocks);
    }
  }
}

TEST(ProceduralAssertionQueueRun,
     EachReachInALoopQueuesItsOwnInstanceForEachKind) {
  for (const char* directive : kQueueDirectives) {
    SCOPED_TRACE(directive);
    std::string body = "    for (int i = 0; i < 2; i++) begin\n      " +
                       QueueStatement(directive, "fast", "f") + "\n      " +
                       QueueStatement(directive, "slow", "s") + "\n    end\n";
    SimFixture f;
    std::string out = RunCapture(QueueSource("module", body), f);
    EXPECT_EQ(PlacedSortedVerdicts(out),
              PlacedSortedVerdicts(std::string(kMaturedAtTheirOwnClocks) +
                                   kMaturedAtTheirOwnClocks));
  }
}

constexpr const char* kMulticlockSignals =
    "  logic clk = 0, a = 1, b = 1;\n"
    "  always #5 clk = ~clk;\n"
    "  initial #33 $finish;\n";

constexpr const char* kMulticlockStatement =
    "x1: assert property (@(posedge clk) a ##1 @(negedge clk) b) "
    "$display(\"p %0t\", $time);";

TEST(ProceduralAssertionQueueRun,
     DISABLED_AMulticlockedPropertyInAnInterfaceOrCheckerProcedureCounts) {
  for (const char* unit : {"interface", "checker"}) {
    SCOPED_TRACE(unit);
    bool checker = std::string(unit) == "checker";
    std::string src =
        checker
            ? "checker w(clk, a, b);\n  always_ff @(posedge clk) "
            : "interface w(input logic clk, a, b);\n  always @(posedge clk) ";
    src.append(kMulticlockStatement).append("\nend").append(unit);
    src.append("\nmodule t;\n").append(kMulticlockSignals);
    src.append("  w u(clk, a, b);\nendmodule\n");
    SimFixture f;
    std::string out = RunCapture(src, f);
    EXPECT_EQ(out, "p 10\np 20\np 30\n$finish at time 33\n");
  }
}

TEST(
    ProceduralAssertionQueueRun,
    DISABLED_AMulticlockedPropertyQueuedAtAnotherEventBeginsAtItsLeadingClock) {
  SimFixture f;
  std::string out = RunCapture("module t;\n" + std::string(kMulticlockSignals) +
                                   "  always @(negedge clk) " +
                                   kMulticlockStatement + "\nendmodule\n",
                               f);
  EXPECT_EQ(out, "p 20\np 30\n$finish at time 33\n");
}

}  // namespace
