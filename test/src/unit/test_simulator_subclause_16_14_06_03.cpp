#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

std::string GlitchSource(const std::string& procedures) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic en = 1, foo = 0, bar = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) bar <= ~bar;\n" +
         procedures +
         "  initial begin\n"
         "    #20 en = 0;\n"
         "    #20 $finish;\n"
         "  end\n"
         "endmodule\n";
}

const char* const kBlock2 =
    "  always_comb begin : procedural_block_2\n"
    "    p1: assert property (@(posedge clk) (const'(foo) == const'(bar)))\n"
    "      $display(\"p1 passed at %0d\", $time);\n"
    "    else $display(\"p1 failed at %0d\", $time);\n"
    "  end\n";

TEST(ProceduralAssertionGlitchRun, AFlushDropsTheGlitchOfProceduralOrder) {
  SimFixture f;
  std::string out =
      RunCapture(GlitchSource("  always_comb begin : procedural_block_1\n"
                              "    if (en) foo = bar;\n"
                              "  end\n" +
                              std::string(kBlock2)),
                 f);
  EXPECT_EQ(out,
            "p1 passed at 5\np1 passed at 5\np1 passed at 15\n"
            "p1 failed at 25\np1 passed at 35\n$finish at time 40\n");
}

TEST(ProceduralAssertionGlitchRun,
     AReactiveRegionWriteQueuesAnAttemptTooLateToPreventTheReport) {
  SimFixture f;
  std::string out = RunCapture(
      GlitchSource(std::string(kBlock2) +
                   "  program reactive_driver;\n"
                   "    initial forever @(posedge clk) if (!en) foo = bar;\n"
                   "  endprogram\n"),
      f);
  EXPECT_EQ(out,
            "p1 passed at 5\np1 failed at 5\np1 passed at 15\n"
            "p1 failed at 25\np1 passed at 25\n"
            "p1 failed at 35\np1 passed at 35\n$finish at time 40\n");
}

constexpr const char* kGlitchDirectives[] = {
    "assert property", "assume property", "cover property", "cover sequence"};

bool IsGlitchCover(const std::string& directive) {
  return directive.starts_with("cover");
}

std::string GlitchStatement(const std::string& directive) {
  if (IsGlitchCover(directive)) {
    return "x1: " + directive +
           " (@(posedge clk) const'(foo) != const'(bar)) "
           "$display(\"p %0t\", $time);";
  }
  return "x1: " + directive +
         " (@(posedge clk) const'(foo) == const'(bar)) "
         "$display(\"p %0t\", $time); else $display(\"f %0t\", $time);";
}

constexpr const char* kOrderWriter = "  always @(bar) #0 foo = bar;\n";

constexpr const char* kReactiveWriter =
    "  program r;\n    initial begin #2; foo = bar; #10; end\n  endprogram\n";

std::string PlacedGlitchSource(const std::string& place,
                               const std::string& procedure,
                               const std::string& directive, bool reactive) {
  std::string checked =
      "  " + procedure + " begin " + GlitchStatement(directive) + " end\n";
  std::string top =
      "  logic clk = 0, foo = 0, bar = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  initial #2 bar = 1;\n"
      "  initial #8 $finish;\n";
  top += reactive ? kReactiveWriter : kOrderWriter;
  if (place == "module") {
    return "module t;\n" + top + checked + "endmodule\n";
  }
  if (place == "generate") {
    return "module t;\n" + top + "  if (1) begin : g\n" + checked +
           "  end\nendmodule\n";
  }
  std::string header = place == "checker"
                           ? "checker w(clk, foo, bar);\n"
                           : "interface w(input logic clk, foo, bar);\n";
  return header + checked + "end" + place + "\nmodule t;\n" + top +
         "  w u(clk, foo, bar);\nendmodule\n";
}

struct GlitchProcedure {
  const char* procedure;
  bool runs_at_time_zero;
};

constexpr GlitchProcedure kGlitchProcedures[] = {
    {"always_comb", true},
    {"always_latch", true},
    {"always @(foo or bar)", false}};

std::string GlitchExpected(const std::string& directive,
                           const GlitchProcedure& procedure, bool reactive) {
  std::string out;
  if (IsGlitchCover(directive)) return reactive ? "p 5\n" : "";
  if (reactive) out += "f 5\n";
  out += "p 5\n";
  if (procedure.runs_at_time_zero) out += "p 5\n";
  return out;
}

void ExpectGlitchesInEachPlace(bool reactive) {
  for (const char* place : {"module", "generate", "interface", "checker"}) {
    for (const GlitchProcedure& procedure : kGlitchProcedures) {
      if (std::string(place) == "checker" && !procedure.runs_at_time_zero) {
        continue;
      }
      for (const char* directive : kGlitchDirectives) {
        std::string src =
            PlacedGlitchSource(place, procedure.procedure, directive, reactive);
        SCOPED_TRACE(src);
        SimFixture f;
        EXPECT_EQ(PlacedSortedVerdicts(RunCapture(src, f)),
                  GlitchExpected(directive, procedure, reactive));
      }
    }
  }
}

TEST(ProceduralAssertionGlitchRun,
     AGlitchOfProceduralOrderIsFlushedForEachKindInEachPlace) {
  ExpectGlitchesInEachPlace(false);
}

TEST(ProceduralAssertionGlitchRun,
     AGlitchOfAReactiveWriteIsReportedForEachKindInEachPlace) {
  ExpectGlitchesInEachPlace(true);
}

}  // namespace
