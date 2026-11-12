#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

const char kGlobal[] = "@($global_clock) ";

std::string TrigBench(const std::string& items,
                      const std::string& outside = "") {
  return outside +
         "module ev; event e; endmodule\n"
         "module cs(input logic rclk);\n"
         "  sequence s; @(posedge rclk) 1; endsequence\n"
         "endmodule\n"
         "interface ie_if; event ie; endinterface\n"
         "interface sif(input logic clk);\n"
         "  sequence s; @(posedge clk) 1; endsequence\n"
         "endinterface\n"
         "program pg(input logic clk);\n"
         "  initial forever @(posedge clk) begin\n"
         "    -> top.pe; -> top.u.e; top.rclk = 1; #2 top.rclk = 0;\n"
         "  end\n"
         "endprogram\n"
         "module top;\n"
         "  logic clk = 0, rclk = 0, b = 1, en = 0; int n = 0;\n"
         "  event e, pe;\n"
         "  sequence s; @(posedge clk) 1; endsequence\n"
         "  sequence rs; @(posedge rclk) 1; endsequence\n"
         "  clocking cb @(posedge clk); sequence cs1; 1; endsequence "
         "endclocking\n"
         "  global clocking gc @(posedge clk); endclocking\n"
         "  ev u(); cs uc(rclk); ie_if i(); sif si(clk); pg p(clk);\n"
         "  always @(posedge clk) n <= n + 1;\n"
         "  initial repeat (8) begin\n"
         "    #5; if (!clk) begin -> e; -> i.ie; end clk = ~clk;\n"
         "  end\n"
         "  " +
         items +
         "\n"
         "endmodule\n";
}

std::string AtFirstTick(const std::string& expr) {
  return "n != 0 || (" + expr + ")";
}

void ExpectAtFirstTick(std::initializer_list<const char*> exprs,
                       const std::string& clock = "@(posedge clk) ") {
  for (const char* expr : exprs) {
    ExpectOnlyPasses(TrigBench(SampledVerdict(AtFirstTick(expr), clock)));
  }
}

std::string RoseFromDefault(const std::string& m) {
  return "$rose(" + m + ") && !$fell(" + m + ") && !$stable(" + m +
         ") && $changed(" + m + ")";
}

TEST(TriggeredDefaultSampling, DISABLED_APastTriggeredAtTheFirstTickIsZero) {
  ExpectAtFirstTick({"e.triggered && $past(e.triggered) == 0",
                     "s.triggered && $past(s.triggered) == 0"});
}

TEST(TriggeredDefaultSampling,
     DISABLED_AValueChangeAtTheFirstTickComparesWithZero) {
  for (const char* m : {"e.triggered", "s.triggered"}) {
    ExpectOnlyPasses(
        TrigBench(SampledVerdict(AtFirstTick(RoseFromDefault(m)))));
  }
}

TEST(TriggeredDefaultSampling,
     DISABLED_AnExpressionsDefaultIsBuiltFromItsParts) {
  ExpectAtFirstTick({"$fell(!e.triggered)", "$past(e.triggered && b) == 0"});
}

TEST(TriggeredDefaultSampling, DISABLED_ADelayedPastReadsZeroForEachEarlyTick) {
  ExpectOnlyPasses(TrigBench(
      SampledVerdict("n >= 2 || (e.triggered && $past(e.triggered, 2) == 0)")));
}

TEST(TriggeredDefaultSampling, DISABLED_AGatedPastReadsZeroUntilTheGateHeld) {
  ExpectOnlyPasses(TrigBench(
      SampledVerdict("e.triggered && $past(e.triggered, 1, en) == 0")));
}

std::string GclkPastFromDefault(const std::string& m) {
  return "$past_gclk(" + m + ") == 0 && $rose_gclk(" + m + ") && !$fell_gclk(" +
         m + ") && !$stable_gclk(" + m + ") && $changed_gclk(" + m + ")";
}

TEST(TriggeredDefaultSampling,
     DISABLED_AGlobalClockPastAtTheFirstTickComparesWithZero) {
  for (const char* m : {"e.triggered", "s.triggered"}) {
    ExpectOnlyPasses(TrigBench(
        SampledVerdict(AtFirstTick(GclkPastFromDefault(m)), kGlobal)));
  }
}

TEST(TriggeredDefaultSampling,
     DISABLED_AProceduralCallAtTheFirstTickComparesWithZero) {
  ExpectOnlyPasses(TrigBench(
      "always @(posedge clk) if (n == 0) " +
      ProceduralVerdict("$past(e.triggered) == 0 && $rose(e.triggered)")));
}

TEST(TriggeredDefaultSampling,
     DISABLED_AnInterfacesEventReachedByNameDefaultsToZero) {
  ExpectAtFirstTick(
      {"i.ie.triggered && $past(i.ie.triggered) == 0 && "
       "$rose(i.ie.triggered)"});
}

TEST(TriggeredDefaultSampling, AnInstancesEventReachedByNameDefaultsToZero) {
  ExpectAtFirstTick({"$past(u.e.triggered) == 0"});
}

TEST(TriggeredDefaultSampling, DISABLED_ASequenceOfEveryPlaceDefaultsToZero) {
  ExpectAtFirstTick(
      {"si.s.triggered && $past(si.s.triggered) == 0 && "
       "$rose(si.s.triggered)",
       "cb.cs1.triggered && $past(cb.cs1.triggered) == 0 && "
       "$rose(cb.cs1.triggered)"});
  ExpectOnlyPasses(
      TrigBench("chk k(clk, n);",
                "checker chk(logic c, int m);\n"
                "  sequence q; @(posedge c) 1; endsequence\n  " +
                    SampledVerdict("m != 0 || ($past(q.triggered) == 0 && "
                                   "$rose(q.triggered))",
                                   "@(posedge c) ") +
                    "\nendchecker\n"));
}

std::string AfterFirstTick(const std::string& expr) {
  return "n == 0 || (" + expr + ")";
}

void ExpectAfterFirstTick(std::initializer_list<std::string> exprs,
                          const std::string& clock = "@(posedge clk) ") {
  for (const auto& expr : exprs) {
    ExpectOnlyPasses(TrigBench(SampledVerdict(AfterFirstTick(expr), clock)));
  }
}

std::string FellAcrossTick(const std::string& m, const std::string& suffix) {
  return "$fell" + suffix + "(" + m + ") && !$rose" + suffix + "(" + m +
         ") && !$stable" + suffix + "(" + m + ") && $changed" + suffix + "(" +
         m + ")";
}

TEST(TriggeredPostponedSampling, APastOfAReactiveTriggerIsItsPostponedValue) {
  ExpectAfterFirstTick({"!pe.triggered && $past(pe.triggered)",
                        "!rs.triggered && $past(rs.triggered)"});
}

TEST(TriggeredPostponedSampling, AValueChangeSeesTheReactiveTrigger) {
  ExpectAfterFirstTick(
      {FellAcrossTick("pe.triggered", ""), FellAcrossTick("rs.triggered", "")});
}

TEST(TriggeredPostponedSampling,
     DISABLED_AGlobalClockPastSeesTheReactiveTrigger) {
  ExpectAfterFirstTick(
      {"$past_gclk(pe.triggered) && " + FellAcrossTick("pe.triggered", "_gclk"),
       "$past_gclk(rs.triggered) && " +
           FellAcrossTick("rs.triggered", "_gclk")},
      kGlobal);
}

TEST(TriggeredPostponedSampling, ADelayedGatedOrReclockedPastSeesIt) {
  ExpectOnlyPasses(
      TrigBench(SampledVerdict("n < 2 || $past(pe.triggered, 2)")));
  ExpectAfterFirstTick({"$past(pe.triggered, 1, b)",
                        "$past(pe.triggered, 1, 1, @(posedge clk))"});
}

std::string RisingIntoTick(const std::string& m) {
  return "$future_gclk(" + m + ") && $rising_gclk(" + m +
         ") && !$falling_gclk(" + m + ") && !$steady_gclk(" + m +
         ") && $changing_gclk(" + m + ")";
}

TEST(TriggeredPostponedSampling,
     DISABLED_AFutureOfAReactiveTriggerIsItsPostponedValue) {
  for (const char* m : {"pe.triggered", "rs.triggered"}) {
    ExpectOnlyPasses(TrigBench(SampledVerdict(RisingIntoTick(m), kGlobal)));
  }
}

TEST(TriggeredPostponedSampling, AnEventOrSequenceReachedByNameIsPostponed) {
  ExpectAfterFirstTick({"!u.e.triggered && $past(u.e.triggered)",
                        "!uc.s.triggered && $past(uc.s.triggered)"});
}

TEST(TriggeredPostponedSampling, AnInterfaceProgramOrCheckersOwnIsPostponed) {
  ExpectOnlyPasses(TrigBench(
      "ift it(clk); ptr pt(clk);",
      "interface ift(input logic clk);\n"
      "  event ev2; int m = 0;\n"
      "  always @(posedge clk) m <= m + 1;\n  " +
          SampledVerdict("m == 0 || (!ev2.triggered && $past(ev2.triggered))") +
          "\nendinterface\n"
          "program ptr(input logic clk);\n"
          "  initial forever @(posedge clk) -> top.it.ev2;\n"
          "endprogram\n"));
  ExpectOnlyPasses(TrigBench(
      "pown po(clk);",
      "program pown(input logic clk);\n"
      "  event ev3; int m = 0;\n"
      "  initial forever @(posedge clk) begin m = m + 1; -> ev3; end\n"
      "  " +
          SampledVerdict("m < 2 || $past(ev3.triggered)") + "\nendprogram\n"));
  ExpectOnlyPasses(TrigBench(
      "cpk k(clk, rclk, n);",
      "checker cpk(logic c, logic r, int m);\n"
      "  sequence q; @(posedge r) 1; endsequence\n  " +
          SampledVerdict("m == 0 || (!q.triggered && $past(q.triggered))",
                         "@(posedge c) ") +
          "\nendchecker\n"));
}

TEST(TriggeredPostponedSampling, AProceduralAssertionSeesIt) {
  ExpectOnlyPasses(
      TrigBench("always @(posedge clk) " +
                SampledVerdict(AfterFirstTick("$past(pe.triggered)"), "")));
}

TEST(TriggeredPostponedSampling, DISABLED_AProceduralGlobalClockCallSeesIt) {
  ExpectOnlyPasses(TrigBench("always @(posedge clk) if (n != 0) " +
                             ProceduralVerdict("$past_gclk(pe.triggered)")));
}

}  // namespace
