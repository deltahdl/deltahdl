#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

const char kGlobal[] = "@($global_clock) ";

std::string Checker(const std::string& items) {
  return "checker chk(logic clk, logic [3:0] cnt);\n"
         "  rand bit [3:0] r;\n"
         "  m1: assume property (@(posedge clk) r == cnt);\n"
         "  " +
         items + "\nendchecker\n";
}

std::string FreeBench(const std::string& items,
                      const std::string& instance = "chk c(clk, cnt);",
                      const std::string& outside = "") {
  return Checker(items) + outside +
         "module top;\n"
         "  logic clk = 0; logic [3:0] cnt = 0;\n"
         "  global clocking gc @(posedge clk); endclocking\n"
         "  always #5 clk = ~clk;\n"
         "  always @(negedge clk) cnt = cnt + 1;\n"
         "  " +
         instance +
         "\n"
         "  initial #42 $finish;\n"
         "endmodule\n";
}

void ExpectEachInChecker(std::initializer_list<const char*> exprs,
                         const std::string& clock = "@(posedge clk) ") {
  for (const char* expr : exprs) {
    ExpectOnlyPasses(FreeBench(SampledVerdict(expr, clock)));
  }
}

const char kPast[] = "##1 $past(r) == $past(cnt)";

TEST(FreeCheckerVariableSampling, APastIsThePostponedValueOfThePastTick) {
  ExpectEachInChecker({kPast});
}

TEST(FreeCheckerVariableSampling, ADelayedGatedOrReclockedPastIsPostponed) {
  ExpectEachInChecker({"##2 $past(r, 2) == $past(cnt, 2)",
                       "##1 $past(r, 1, 1'b1) == $past(cnt)",
                       "##1 $past(r, 1, , @(negedge clk)) == $past(cnt)"});
}

TEST(FreeCheckerVariableSampling, AValueChangeComparesWithThePostponedValue) {
  ExpectEachInChecker(
      {"##1 ($changed(r) && !$stable(r) && "
       "$rose(r[0]) == cnt[0] && $fell(r[0]) == !cnt[0])"});
}

TEST(FreeCheckerVariableSampling,
     DISABLED_AGlobalClockPastIsThePostponedValue) {
  ExpectEachInChecker(
      {"##1 ($past_gclk(r) == $past(cnt) && $changed_gclk(r) && "
       "!$stable_gclk(r) && $rose_gclk(r[0]) == cnt[0] && "
       "$fell_gclk(r[0]) == !cnt[0])"},
      kGlobal);
}

TEST(FreeCheckerVariableSampling,
     DISABLED_AGlobalClockFutureIsThePostponedValue) {
  ExpectEachInChecker(
      {"$future_gclk(r) == $future_gclk(cnt) && $changing_gclk(r) && "
       "!$steady_gclk(r) && $rising_gclk(r[0]) == !cnt[0] && "
       "$falling_gclk(r[0]) == cnt[0]"},
      kGlobal);
}

TEST(FreeCheckerVariableSampling, AnotherClocksPastReadsTheSolvedValue) {
  ExpectEachInChecker({"##1 (clk != 1'b1 || $past(r) == cnt)"}, "@(edge clk) ");
}

TEST(FreeCheckerVariableSampling,
     DISABLED_AnActiveElementBesideAnInactiveOneIsPostponed) {
  ExpectOnlyPasses(
      FreeBench("rand bit [3:0] ra [2];\n"
                "  always_ff @(posedge clk) ra[0] <= cnt;\n"
                "  m2: assume property (@(posedge clk) ra[1] == cnt);\n  " +
                SampledVerdict("##1 $past(ra[1]) == $past(cnt)")));
}

TEST(FreeCheckerVariableSampling,
     EveryPlaceOfTheCheckerReadsThePostponedValue) {
  const std::string kItems = SampledVerdict(kPast);
  struct Place {
    const char* instance;
    const char* outside;
  };
  for (const Place& p :
       {Place{"hi i(clk, cnt);",
              "interface hi(input logic clk, input logic [3:0] cnt);\n"
              "  chk c(clk, cnt);\nendinterface\n"},
        Place{"hp p(clk, cnt);",
              "program hp(input logic clk, input logic [3:0] cnt);\n"
              "  chk c(clk, cnt);\n  initial #42;\nendprogram\n"},
        Place{"outer o(clk, cnt);",
              "checker outer(logic clk, logic [3:0] cnt);\n"
              "  chk c(clk, cnt);\nendchecker\n"},
        Place{"if (1) begin : g chk c(clk, cnt); end", ""},
        Place{"always @(posedge clk) begin chk c(clk, cnt); end", ""}}) {
    ExpectOnlyPasses(FreeBench(kItems, p.instance, p.outside));
  }
}

TEST(FreeCheckerVariableSampling, AnInactiveVariablesPastIsPreponed) {
  ExpectOnlyPasses(
      FreeBench("rand bit [3:0] s;\n"
                "  always_ff @(posedge clk) s <= cnt;\n  " +
                SampledVerdict("##2 $past(s) == $past(cnt, 2)")));
  ExpectOnlyPasses(FreeBench("rand const bit [3:0] rc = 4'd6;\n  " +
                             SampledVerdict("##1 $past(rc) == 4'd6")));
}

TEST(FreeCheckerVariableSampling, AFreeVariableReadDirectlyIsTheSolvedValue) {
  ExpectEachInChecker({"r == cnt"});
}

}  // namespace
