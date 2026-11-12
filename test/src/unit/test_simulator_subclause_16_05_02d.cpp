#include <gtest/gtest.h>

#include <string>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

const char kGateVerdicts[] = "15 fail 25 pass";

std::string GateBench(const std::string& items,
                      const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0, en = 0;\n"
         "  initial begin\n"
         "    #5 clk = 1; #5 clk = 0;\n"
         "    #5 en = 1; clk = 1; #5 clk = 0;\n"
         "    #5 clk = 1; #5 clk = 0;\n"
         "  end\n"
         "  " +
         items +
         "\n"
         "endmodule\n";
}

std::string Verdict(const std::string& head) {
  return head +
         " $display(\"V%0t pass\", $time); else $display(\"V%0t fail\", "
         "$time);";
}

const char kGated[] = "assert property (@(posedge clk iff en) en)";

TEST(AssertionClockExpression, AGateReadsCurrentAndTheBodyReadsSampled) {
  ExpectLines(GateBench(Verdict(kGated)), "V", kGateVerdicts);
}

TEST(AssertionClockExpression, AGatedAssumptionOrCoverIsTheSame) {
  ExpectLines(GateBench(Verdict("assume property (@(posedge clk iff en) en)")),
              "V", kGateVerdicts);
  ExpectLines(GateBench("cover property (@(posedge clk iff en) en) "
                        "$display(\"V%0t pass\", $time);"),
              "V", "25 pass");
}

TEST(AssertionClockExpression, TheClocksOwnValueChangeIsSampled) {
  ExpectLines(GateBench(Verdict("assert property (@(posedge clk) !$rose(clk) "
                                "&& $past(clk) == 1'b0)")),
              "V", "5 pass 15 pass 25 pass");
}

TEST(AssertionClockExpression, AProceduralGatedClockIsTheSame) {
  ExpectLines(GateBench("always @(posedge clk iff en) " +
                        Verdict("assert property (en)")),
              "V", kGateVerdicts);
}

const char kPorts[] = "(input logic clk, en)";

std::string Unit(const char* kind) {
  return std::string(kind) + " u_unit" + kPorts + ";\n  " + Verdict(kGated) +
         "\n  initial #40;\nend" + kind + "\n";
}

TEST(AssertionClockExpression, EveryPlaceReadsTheGateCurrentAndBodySampled) {
  for (const char* kind : {"interface", "program"}) {
    ExpectLines(GateBench("u_unit u(clk, en);", Unit(kind)), "V",
                kGateVerdicts);
  }
  ExpectLines(
      GateBench("ck k(clk, en);", "checker ck(logic clk, logic en);\n  " +
                                      Verdict(kGated) + "\nendchecker\n"),
      "V", kGateVerdicts);
  ExpectLines(GateBench("if (1) begin : g " + Verdict(kGated) + " end"), "V",
              kGateVerdicts);
}

}  // namespace
