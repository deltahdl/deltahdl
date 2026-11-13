#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

constexpr const char* kFlushDirectives[] = {
    "assert property", "assume property", "cover property", "cover sequence"};

bool IsCover(const std::string& directive) {
  return directive.starts_with("cover");
}

std::string Queued(const std::string& directive, const std::string& label) {
  std::string shown = "$display(\"" + label + " %0t\", $time);";
  if (IsCover(directive)) {
    return label + ": " + directive + " (@(posedge clk) 1) " + shown;
  }
  return label + ": " + directive + " (@(posedge clk) 0) else " + shown;
}

struct FlushRow {
  const char* block;
  const char* wake;
};

constexpr const char* kFlushDeclarations =
    "  logic s = 0, u = 0, one = 1, q;\n"
    "  event ev, ev2;\n"
    "  task automatic w; @ev; endtask\n";

std::string BlockingProcesses(const std::string& directive,
                              const FlushRow& row) {
  std::string items = kFlushDeclarations;
  items.append("  initial begin\n    #2;\n    ")
      .append(Queued(directive, "x1"))
      .append("\n    ")
      .append(row.block)
      .append("\n    $display(\"r %0t\", $time);\n  end\n")
      .append("  initial begin #2; #0; ")
      .append(row.wake)
      .append(" end\n");
  return items;
}

std::string InPlace(const std::string& place, const std::string& items) {
  const char* top =
      "  logic clk = 0;\n  always #5 clk = ~clk;\n  initial #8 $finish;\n";
  if (place == "module") return "module t;\n" + (top + items) + "endmodule\n";
  if (place == "generate") {
    return "module t;\n" + (top + ("  if (1) begin : g\n" + items)) +
           "  end\nendmodule\n";
  }
  std::string header = place == "checker" ? "checker w(clk);\n"
                                          : place + " w(input logic clk);\n";
  return header + items + "end" + place + "\nmodule t;\n" + top +
         "  w u(clk);\nendmodule\n";
}

void ExpectRun(const std::string& src, const char* expected) {
  SCOPED_TRACE(src);
  SimFixture f;
  EXPECT_EQ(PlacedSortedVerdicts(RunCapture(src, f)), expected);
}

constexpr FlushRow kBlockingFlushPoints[] = {
    {"@ev;", "-> ev;"},       {"@(posedge s);", "s = 1;"},
    {"@(s or u);", "s = 1;"}, {"@(posedge s iff one);", "s = 1;"},
    {"@* q = s;", "s = 1;"},  {"w();", "-> ev;"},
    {"wait (s);", "s = 1;"},  {"wait_order (ev, ev2);", "-> ev; #0 -> ev2;"}};

TEST(ProceduralAssertionFlushPointsRun,
     EachEventControlOrWaitThatBlocksFlushesForEachKind) {
  for (const char* directive : kFlushDirectives) {
    for (const FlushRow& row : kBlockingFlushPoints) {
      ExpectRun(InPlace("module", BlockingProcesses(directive, row)), "r 2\n");
    }
  }
}

TEST(ProceduralAssertionFlushPointsRun,
     AnEventControlThatBlocksFlushesInAGenerateBlockAnInterfaceAndAProgram) {
  for (const char* place : {"generate", "interface", "program"}) {
    for (const char* directive : kFlushDirectives) {
      ExpectRun(
          InPlace(place, BlockingProcesses(directive, {"@ev;", "-> ev;"})),
          "r 2\n");
      ExpectRun(
          InPlace(place, BlockingProcesses(directive, {"wait (s);", "s = 1;"})),
          "r 2\n");
    }
  }
}

constexpr FlushRow kUnflushedBlockingPoints[] = {
    {"fork begin #0; end join_none wait fork;", ""},
    {"q = @ev s;", "-> ev;"},
    {"q = repeat (2) @ev s;", "-> ev; #0 -> ev;"}};

TEST(ProceduralAssertionFlushPointsRun,
     DISABLED_AWaitForkOrABlockingIntraAssignmentControlThatBlocksFlushes) {
  for (const char* directive : kFlushDirectives) {
    for (const FlushRow& row : kUnflushedBlockingPoints) {
      ExpectRun(InPlace("module", BlockingProcesses(directive, row)), "r 2\n");
    }
  }
}

constexpr FlushRow kNoFlushPoints[] = {{"#0;", ""},
                                       {"wait (one);", ""},
                                       {"wait fork;", ""},
                                       {"q <= @ev s;", "-> ev;"}};

TEST(ProceduralAssertionFlushPointsRun,
     WhatDoesNotBlockOnAnEventOrWaitLetsTheInstanceMatureForEachKind) {
  for (const char* directive : kFlushDirectives) {
    for (const FlushRow& row : kNoFlushPoints) {
      ExpectRun(InPlace("module", BlockingProcesses(directive, row)),
                "r 2\nx1 5\n");
    }
  }
}

std::string RerunStatement(const std::string& directive) {
  if (IsCover(directive)) {
    return "x1: " + directive +
           " (@(posedge clk) const'(s) != const'(u)) "
           "$display(\"p %0t\", $time);";
  }
  return "x1: " + directive +
         " (@(posedge clk) const'(s) == const'(u)) "
         "$display(\"p %0t\", $time); else $display(\"f %0t\", $time);";
}

constexpr const char* kRerunStimulus =
    "  initial begin #2 s = 1; #0 u = 1; end\n";

std::string RerunSource(const std::string& place, const std::string& kind,
                        const std::string& directive) {
  std::string procedure = "  " + kind + " begin " + RerunStatement(directive);
  if (place == "checker") {
    return "checker w(clk, s, u);\n" + procedure +
           " end\nendchecker\nmodule t;\n"
           "  logic clk = 0, s = 0, u = 0;\n"
           "  always #5 clk = ~clk;\n"
           "  initial #8 $finish;\n" +
           kRerunStimulus + "  w c(clk, s, u);\nendmodule\n";
  }
  return InPlace(place, "  logic s = 0, u = 0, q;\n" + procedure +
                            " q = s; end\n" + kRerunStimulus);
}

TEST(ProceduralAssertionFlushPointsRun,
     AnAlwaysCombOrAlwaysLatchRunAgainFlushesForEachKindInEachPlace) {
  for (const char* place : {"module", "generate", "interface", "checker"}) {
    for (const char* kind : {"always_comb", "always_latch"}) {
      for (const char* directive : kFlushDirectives) {
        ExpectRun(RerunSource(place, kind, directive),
                  IsCover(directive) ? "" : "p 5\np 5\n");
      }
    }
  }
}

TEST(ProceduralAssertionFlushPointsRun,
     AFlushClearsOnlyTheQueueOfTheProcessThatReachesItForEachKind) {
  for (const char* directive : kFlushDirectives) {
    std::string items = "  event ev;\n  initial begin #2; ";
    items.append(Queued(directive, "x1"))
        .append(" @ev; end\n  initial begin #2; ")
        .append(Queued(directive, "x2"))
        .append(" #0 -> ev; end\n");
    ExpectRun(InPlace("module", items), "x2 5\n");
  }
}

}  // namespace
