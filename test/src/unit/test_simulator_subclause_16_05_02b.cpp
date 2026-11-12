#include <gtest/gtest.h>

#include <string>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

const char kPosedges[] = "5 15 25 35";
const char kNegedges[] = "10 20 30";
const char kTick[] = "$display(\"T%0t\", $time);";

std::string GlobalBench(const std::string& items,
                        const std::string& outside = "",
                        const char* edge = "posedge") {
  return outside +
         "module top;\n"
         "  logic clk = 0, a = 0, en = 0;\n"
         "  global clocking gc @(" +
         edge +
         " clk); endclocking\n"
         "  always #5 clk = ~clk;\n"
         "  " +
         items +
         "\n"
         "  initial #38 $finish;\n"
         "endmodule\n";
}

std::string Ticked(const std::string& head) { return head + " " + kTick; }

TEST(GlobalClockAssertion, AnAssumptionIsAttemptedAtEachGlobalTick) {
  ExpectLines(GlobalBench(Ticked("assume property (@$global_clock 1)")), "T",
              kPosedges);
}

TEST(GlobalClockAssertion, ACoverSequenceIsAttemptedAtEachGlobalTick) {
  ExpectLines(GlobalBench(Ticked("cover sequence (@$global_clock 1)")), "T",
              kPosedges);
}

TEST(GlobalClockAssertion, AnExpectWaitsForTheGlobalTick) {
  ExpectLines(GlobalBench("initial begin\n"
                          "    #1 expect (@$global_clock 1) " +
                          std::string(kTick) +
                          "\n"
                          "    #1 expect (@$global_clock 1) " +
                          kTick + "\n  end"),
              "T", "5 15");
}

TEST(GlobalClockAssertion, AGatedGlobalClockSkipsTheTicksItsGateHolds) {
  ExpectLines(
      GlobalBench("initial begin #12 en = 1; #10 en = 0; end\n  " +
                  Ticked("assert property (@($global_clock iff en) 1)")),
      "T", "15");
}

TEST(GlobalClockAssertion, AProceduralAssertionWaitsForTheGlobalTick) {
  ExpectLines(GlobalBench("always @(negedge clk) " +
                          Ticked("assert property (@$global_clock 1)")),
              "T", "15 25 35");
}

TEST(GlobalClockAssertion, TheVerdictReadsTheValueSampledAtTheTick) {
  ExpectLines(GlobalBench("initial #15 a = 1;\n  "
                          "assert property (@$global_clock a) "
                          "$display(\"V%0t pass\", $time); "
                          "else $display(\"V%0t fail\", $time);"),
              "V", "5 fail 15 fail 25 pass 35 pass");
}

std::string Unit(const char* kind, const char* own) {
  return std::string(kind) + " u_unit(input logic clk);\n  " + own + "\n  " +
         Ticked("assert property (@$global_clock 1)") +
         "\n  initial #40;\nend" + kind + "\n";
}

const char kOwnNegedge[] = "global clocking uc @(negedge clk); endclocking";

TEST(GlobalClockAssertion, AnInterfaceOrProgramUsesItsOwnDeclaration) {
  for (const char* kind : {"interface", "program"}) {
    ExpectLines(GlobalBench("u_unit u(clk);", Unit(kind, kOwnNegedge)), "T",
                kNegedges);
  }
}

TEST(GlobalClockAssertion, AnInterfaceOrProgramWithoutOneUsesItsParents) {
  for (const char* kind : {"interface", "program"}) {
    ExpectLines(GlobalBench("u_unit u(clk);", Unit(kind, "")), "T", kPosedges);
  }
}

std::string CheckerUnit(const char* own) {
  return std::string("checker ck(logic clk);\n  ") + own + "\n  " +
         Ticked("assert property (@$global_clock 1)") + "\nendchecker\n";
}

TEST(GlobalClockAssertion, ACheckerUsesItsOwnDeclaration) {
  ExpectLines(GlobalBench("ck k(clk);", CheckerUnit(kOwnNegedge)), "T",
              kNegedges);
}

TEST(GlobalClockAssertion, ACheckerWithoutOneUsesTheInstantiatingModules) {
  ExpectLines(GlobalBench("ck k(clk);", CheckerUnit("")), "T", kPosedges);
}

TEST(GlobalClockAssertion, EachInstanceOfAChildUsesItsOwnAncestors) {
  ExpectLines(
      GlobalBench(
          "pa ua(clk); pb ub(clk);",
          "module child #(parameter int K = 0)(input logic clk);\n"
          "  assert property (@$global_clock 1) $display(\"T%0d %0t\", K, "
          "$time);\n"
          "endmodule\n"
          "module pa(input logic clk);\n"
          "  global clocking ga @(posedge clk); endclocking\n"
          "  child #(1) c(clk);\n"
          "endmodule\n"
          "module pb(input logic clk);\n"
          "  global clocking gb @(negedge clk); endclocking\n"
          "  child #(2) c(clk);\n"
          "endmodule\n"),
      "T", "1 5 2 10 1 15 2 20 1 25 2 30 1 35");
}

TEST(GlobalClockAssertion, DISABLED_AGenerateBlocksAssertionUsesItsModules) {
  ExpectLines(
      GlobalBench("if (1) begin : gb " +
                  Ticked("assert property (@$global_clock 1)") + " end"),
      "T", kPosedges);
  ExpectLines(
      GlobalBench("for (genvar j = 0; j < 1; j++) begin : lb " +
                      Ticked("assert property (@$global_clock 1)") + " end",
                  "", "negedge"),
      "T", kNegedges);
}

}  // namespace
