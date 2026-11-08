#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

constexpr const char* kStimulus =
    "  initial begin\n"
    "    #5 gclk = 1; #5 gclk = 0;\n"
    "    #5 gclk = 1; clk = 1; -> e; t = 1; #5 gclk = 0;\n"
    "    #5 gclk = 1; t = 0; #5 gclk = 0;\n"
    "    #5 gclk = 1; clk = 0; d = 1; #5 gclk = 0;\n"
    "    #5 gclk = 1; en = 0; #5 gclk = 0;\n"
    "    #5 gclk = 1; clk = 1; d = 0; #5 gclk = 0;\n"
    "    #5 gclk = 1; clk = 0; -> e; t = 1; #5 gclk = 0;\n"
    "    #5 gclk = 1; t = 0; en = 1; #5 gclk = 0;\n"
    "    #5 gclk = 1; clk = 1; #5 gclk = 0;\n"
    "    #5 gclk = 1; #5 gclk = 0;\n"
    "  end\n";

constexpr unsigned kTicks = 10;

std::string Design(const std::string& control, const std::string& rewritten) {
  return "module m;\n"
         "  logic gclk = 0;\n"
         "  logic clk = 0;\n"
         "  logic d = 0;\n"
         "  logic en = 1;\n"
         "  event e;\n"
         "  bit t = 0;\n"
         "  int attempts = 0;\n"
         "  int ticks = 0;\n"
         "  global clocking gc @(posedge gclk); endclocking\n"
         "  assert property (@(" +
         control +
         ") 1'b1) attempts = attempts + 1;\n"
         "  assert property (@$global_clock " +
         rewritten + ") ticks = ticks + 1;\n" + kStimulus + "endmodule\n";
}

void ExpectRewrite(const std::string& control, const std::string& rewritten,
                   unsigned expected) {
  SimFixture f;
  auto* attempts = RunAndFindVar(Design(control, rewritten), f, "attempts");
  ASSERT_NE(attempts, nullptr);
  EXPECT_EQ(attempts->value.ToUint64(), expected);
  auto* ticks = f.ctx.FindVariable("ticks");
  ASSERT_NE(ticks, nullptr);
  EXPECT_EQ(ticks->value.ToUint64(), expected);
}

TEST(ClockControlRewriteSim, GlobalClockIsEveryTick) {
  ExpectRewrite("$global_clock", "1'b1", kTicks);
}

TEST(ClockControlRewriteSim, BareExpressionIsChangingGclk) {
  ExpectRewrite("clk", "$changing_gclk(clk)", 5);
}

TEST(ClockControlRewriteSim, PosedgeIsRisingGclk) {
  ExpectRewrite("posedge clk", "$rising_gclk(clk)", 3);
}

TEST(ClockControlRewriteSim, NegedgeIsFallingGclk) {
  ExpectRewrite("negedge clk", "$falling_gclk(clk)", 2);
}

TEST(ClockControlRewriteSim, EdgeIsRisingOrFallingGclk) {
  ExpectRewrite("edge clk", "$rising_gclk(clk) || $falling_gclk(clk)", 5);
}

TEST(ClockControlRewriteSim, NamedEventIsFutureGclkOfItsDummyBit) {
  ExpectRewrite("e", "$future_gclk(t)", 2);
}

TEST(ClockControlRewriteSim, IffIsConjunctionWithTheGate) {
  ExpectRewrite("posedge clk iff en", "$rising_gclk(clk) && en", 2);
}

TEST(ClockControlRewriteSim, OrIsDisjunction) {
  ExpectRewrite("posedge clk or posedge d",
                "$rising_gclk(clk) || $rising_gclk(d)", 4);
}

TEST(ClockControlRewriteSim, CommaIsDisjunction) {
  ExpectRewrite("negedge clk, negedge d",
                "$falling_gclk(clk) || $falling_gclk(d)", 3);
}

}  // namespace
