#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunClean(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << src;
  return out;
}

std::string TwoClocks(const std::string& outside, const std::string& items) {
  return outside +
         "module t;\n"
         "  logic clk = 0, clk2 = 0, en = 1;\n"
         "  int x = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  initial begin #2; forever #10 clk2 = ~clk2; end\n"
         "  always #1 x = x + 1;\n"
         "  initial begin #20 en = 0; #20 en = 1; end\n"
         "  initial #60 $finish(0);\n" +
         items + "endmodule\n";
}

std::string PerTick(const std::string& call) {
  return "  always @(posedge clk) $display(\"%0d %0d\", $time, " + call +
         ");\n";
}

constexpr const char* kPastAtClk2 = "$past(x, 1, 1, @(posedge clk2))";
constexpr const char* kClk2Ticks = "5 0\n15 11\n25 11\n35 31\n45 31\n55 51\n";

TEST(PastClockingEventRun, DISABLED_AProcedureSamplesAtTheGivenEvent) {
  EXPECT_EQ(RunClean(TwoClocks("", PerTick(kPastAtClk2))), kClk2Ticks);
}

TEST(PastClockingEventRun,
     DISABLED_TwoTicksBackAtTheGivenEventStartsAtTheDefault) {
  EXPECT_EQ(RunClean(TwoClocks("", PerTick("$past(x, 2, , @(posedge clk2))"))),
            "5 0\n15 0\n25 0\n35 11\n45 11\n55 31\n");
}

TEST(PastClockingEventRun,
     DISABLED_AnAssertionsPropertySamplesAtTheGivenEvent) {
  EXPECT_EQ(
      RunClean(TwoClocks("", "  cover property (@(posedge clk) " +
                                 std::string(kPastAtClk2) +
                                 " == 31) $display(\"hit %0d\", $time);\n")),
      "hit 35\nhit 45\n");
  EXPECT_EQ(
      RunClean(TwoClocks(
          "", "  assert property (@(posedge clk) " + std::string(kPastAtClk2) +
                  " != 31) else $display(\"fail %0d\", $time);\n")),
      "fail 35\nfail 45\n");
}

TEST(PastClockingEventRun, DISABLED_AnActionBlockSamplesAtTheGivenEvent) {
  const std::string kShown =
      "$display(\"%0d %0d\", $time, " + std::string(kPastAtClk2) + ")";
  EXPECT_EQ(RunClean(TwoClocks(
                "", "  cover property (@(posedge clk) 1) " + kShown + ";\n")),
            kClk2Ticks);
  EXPECT_EQ(RunClean(TwoClocks(
                "", "  assert property (@(posedge clk) 1) " + kShown + ";\n")),
            kClk2Ticks);
  EXPECT_EQ(RunClean(TwoClocks("",
                               "  assert property (@(posedge clk) 0) "
                               "else " +
                                   kShown + ";\n")),
            kClk2Ticks);
}

TEST(PastClockingEventRun, DISABLED_TheGateAppliesToTheGivenEvent) {
  EXPECT_EQ(
      RunClean(TwoClocks("", PerTick("$past(x, 1, en, @(posedge clk2))"))),
      "5 0\n15 11\n25 11\n35 11\n45 11\n55 51\n");
}

TEST(PastClockingEventRun, DISABLED_AnUnclockedProcedureReadsTheGivenEvent) {
  EXPECT_EQ(
      RunClean(TwoClocks("", "  initial begin\n    #40 $display(\"%0d\", " +
                                 std::string(kPastAtClk2) +
                                 ");\n    #15 $display(\"%0d\", " +
                                 kPastAtClk2 + ");\n  end\n")),
      "31\n51\n");
}

TEST(PastClockingEventRun,
     DISABLED_AFunctionAndAClassMethodSampleAtTheGivenEvent) {
  EXPECT_EQ(RunClean(TwoClocks("", "  function int f(); return " +
                                       std::string(kPastAtClk2) +
                                       "; endfunction\n" + PerTick("f()"))),
            kClk2Ticks);
  EXPECT_EQ(
      RunClean(TwoClocks("", "  class C;\n    function int g(); return " +
                                 std::string(kPastAtClk2) +
                                 "; endfunction\n  endclass\n  C c = new;\n" +
                                 PerTick("c.g()"))),
      kClk2Ticks);
}

TEST(PastClockingEventRun,
     DISABLED_AContinuousAssignmentSamplesAtTheGivenEvent) {
  EXPECT_EQ(RunClean(TwoClocks(
                "", "  int y;\n  assign y = " + std::string(kPastAtClk2) +
                        ";\n  initial begin\n    #40 $display(\"%0d\", y);\n"
                        "    #15 $display(\"%0d\", y);\n  end\n")),
            "31\n51\n");
}

TEST(PastClockingEventRun, DISABLED_AnEventWrittenAsABareIdentifier) {
  EXPECT_EQ(
      RunClean(TwoClocks("", "  event ev;\n  always @(posedge clk2) -> ev;\n" +
                                 PerTick("$past(x, 1, 1, @ev)"))),
      kClk2Ticks);
  EXPECT_EQ(
      RunClean(TwoClocks("", "  clocking cb2 @(posedge clk2); endclocking\n" +
                                 PerTick("$past(x, 1, 1, @cb2)"))),
      kClk2Ticks);
}

TEST(PastClockingEventRun, AnOmittedNumberOfTicksIsOne) {
  constexpr const char* kGatedTicks = "5 0\n15 4\n25 14\n35 14\n45 14\n55 44\n";
  EXPECT_EQ(RunClean(TwoClocks("", PerTick("$past(x, , en)"))), kGatedTicks);
  EXPECT_EQ(RunClean(TwoClocks("", PerTick("$past(x, 1, en)"))), kGatedTicks);
}

TEST(PastClockingEventRun, TooFewPriorTicksGiveTheDefaultSampledValue) {
  EXPECT_EQ(RunClean(TwoClocks(
                "",
                "  logic [7:0] lx;\n  int ix;\n"
                "  always @(x) begin lx = x[7:0]; ix = x; end\n"
                "  always @(posedge clk) $display(\"%0d %0d %0d\", $time, "
                "$past(lx, 3), $past(ix, 3));\n")),
            "5 x 0\n15 x 0\n25 x 0\n35 4 4\n45 14 14\n55 24 24\n");
}

std::string GatedAssertions(const std::string& prefix,
                            const std::string& clock) {
  std::string out =
      "  bit done = 0;\n  int ok = 14, bad = 34;\n"
      "  initial begin #40 done = 1; #10 done = 0; end\n";
  for (const char* name : {"ok", "bad"}) {
    out += prefix;
    out += "assert property (";
    out += clock;
    out += "done |=> (";
    out += name;
    out += " == $past(x, 2, en)))\n    else $display(\"";
    out += name;
    out += " fails at %0d\", $time);\n";
  }
  return out;
}

TEST(PastClockingEventRun, TheClausesGatedPastInAnAssertion) {
  EXPECT_EQ(RunClean(TwoClocks("", GatedAssertions("  ", "@(posedge clk) "))),
            "bad fails at 55\n");
  EXPECT_EQ(
      RunClean(TwoClocks("", GatedAssertions("  always @(posedge clk) ", ""))),
      "bad fails at 55\n");
}

TEST(PastClockingEventRun, DISABLED_AnInterfaceAProgramAndAChecker) {
  const std::string kCover = "  cover property (@(posedge clk) " +
                             std::string(kPastAtClk2) +
                             " == 31) $display(\"hit %0d\", $time);\n";
  EXPECT_EQ(RunClean(TwoClocks("interface ifc(input logic clk, clk2, "
                               "input var int x);\n" +
                                   kCover + "endinterface\n",
                               "  ifc u(clk, clk2, x);\n")),
            "hit 35\nhit 45\n");
  EXPECT_EQ(RunClean(TwoClocks("program pr(input logic clk, clk2, "
                               "input var int x);\n" +
                                   kCover + "endprogram\n",
                               "  pr p(clk, clk2, x);\n")),
            "hit 35\nhit 45\n");
  EXPECT_EQ(RunClean(TwoClocks("checker ck(logic clk, logic clk2, int x);\n" +
                                   kCover + "endchecker\n",
                               "  ck c(clk, clk2, x);\n")),
            "hit 35\nhit 45\n");
}

std::string TwoPhases(const std::string& items, int finish) {
  return "module t;\n"
         "  logic c1 = 0, c2 = 0, a = 0, b = 0, req = 0;\n"
         "  initial forever #10 c1 = ~c1;\n"
         "  initial begin #5; forever #10 c2 = ~c2; end\n" +
         items + "  initial #" + std::to_string(finish) +
         " $finish(0);\nendmodule\n";
}

std::string MulticlockCover(const std::string& call) {
  return TwoPhases(
      "  initial #20 req = 1;\n  int hits = 0;\n"
      "  cover property (@(posedge c1) 1 ##1 @(posedge c2) " +
          call + ") hits++;\n  initial #89 $display(\"hits=%0d\", hits);\n",
      90);
}

TEST(InferredClockRun,
     DISABLED_AnExplicitEventInALaterOperandOfAMulticlockSequence) {
  EXPECT_EQ(RunClean(MulticlockCover("$rose(req, @(posedge c2))")), "hits=1\n");
  EXPECT_EQ(RunClean(MulticlockCover("$rose(req, @(posedge c1))")), "hits=0\n");
}

TEST(InferredClockRun,
     DISABLED_AnUnclockedCallInALaterOperandFollowsTheClockFlow) {
  EXPECT_EQ(RunClean(MulticlockCover("$rose(req)")), "hits=1\n");
}

TEST(InferredClockRun, AnExplicitEventInAnAlwaysFfProcedure) {
  EXPECT_EQ(
      RunClean(TwoClocks(
          "",
          "  logic b = 0, reg1;\n  initial #13 b = 1;\n"
          "  always_ff @(posedge clk) reg1 <= $rose(b, @(posedge clk2));\n"
          "  always @(negedge clk) $display(\"%0d %0d\", $time, reg1);\n")),
      "10 0\n20 1\n30 1\n40 0\n50 0\n");
}

TEST(InferredClockRun, AnUnclockedAssertionUnderTheDefaultClocking) {
  EXPECT_EQ(RunClean(TwoClocks(
                "",
                "  logic a = 0;\n  initial begin #13 a = 1; #20 a = 0; #10 a = "
                "1; end\n"
                "  default clocking @(posedge clk); endclocking\n"
                "  cover property ($rose(a)) $display(\"hit %0d\", $time);\n")),
            "hit 15\nhit 45\n");
}

constexpr const char* kLeadingC1 =
    "10 rose=0 past=0\n30 rose=1 past=0\n50 rose=0 past=1\n70 rose=0 past=1\n";

constexpr const char* kShownRoseAndPast =
    "$display(\"%0d rose=%b past=%b\", $time, $rose(a), $past(a))";

TEST(InferredClockRun, AnActionBlockFollowsTheLeadingClockOverTheDefault) {
  const std::string kItems =
      "  initial #12 a = 1;\n"
      "  default clocking @(posedge c2); endclocking\n";
  EXPECT_EQ(RunClean(TwoPhases(kItems + "  assert property (@(posedge c1) 1) " +
                                   kShownRoseAndPast + ";\n",
                               80)),
            kLeadingC1);
  EXPECT_EQ(
      RunClean(TwoPhases(kItems + "  assert property (@(posedge c1) b) else " +
                             kShownRoseAndPast + ";\n",
                         80)),
      kLeadingC1);
}

TEST(InferredClockRun, DISABLED_AMulticlockActionBlockFollowsTheLeadingClock) {
  EXPECT_EQ(RunClean(TwoPhases(
                "  initial #20 a = 1;\n"
                "  assert property (@(posedge c1) 1 ##1 @(posedge c2) 1) " +
                    std::string(kShownRoseAndPast) + ";\n",
                80)),
            "15 rose=0 past=0\n35 rose=0 past=1\n55 rose=0 past=1\n"
            "75 rose=0 past=1\n");
}

TEST(InferredClockRun, AProceduresClockOutranksTheDefaultClocking) {
  EXPECT_EQ(RunClean(TwoPhases("  initial #12 a = 1;\n"
                               "  default clocking @(posedge c2); endclocking\n"
                               "  always @(posedge c1) " +
                                   std::string(kShownRoseAndPast) + ";\n",
                               80)),
            kLeadingC1);
}

TEST(InferredClockRun, DISABLED_AnInitialProcedureFollowsTheDefaultClocking) {
  const std::string kShown =
      "$display(\"%0d inferred=%b explicit=%b\", $time, $rose(a), "
      "$rose(a, @(posedge clk)))";
  EXPECT_EQ(RunClean("module t;\n"
                     "  logic clk = 0, a = 0;\n"
                     "  always #5 clk = ~clk;\n"
                     "  default clocking @(posedge clk); endclocking\n"
                     "  initial begin\n"
                     "    #12 a = 1;\n"
                     "    #1 " +
                     kShown + ";\n    #4 " + kShown + ";\n    #10 " + kShown +
                     ";\n    $finish(0);\n  end\nendmodule\n"),
            "13 inferred=1 explicit=1\n17 inferred=0 explicit=0\n"
            "27 inferred=0 explicit=0\n");
}

}  // namespace
