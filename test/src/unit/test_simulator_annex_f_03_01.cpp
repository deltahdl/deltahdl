#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

// Annex F.3.1: clock control.
//
// F.3.1 reads every clocking event as a Boolean over the ticks of
// $global_clock, through a rewriting operator that maps $global_clock itself
// to 1, a bare expression to $changing_gclk of it, posedge to $rising_gclk,
// negedge to $falling_gclk, edge to the disjunction of the two, a named event
// to $future_gclk of a dummy bit raised when the event is triggered, an iff
// gate to a conjunction with the gate, and the `or` and comma forms to a
// disjunction. Each case here clocks one assertion on a SystemVerilog event
// control and another on $global_clock with the rewritten Boolean as its
// property, over one word where the two would drift apart if the rewrite were
// wrong, and counts the attempts of the first against the passes of the
// second, which F.3.1 makes the same set of ticks.

using namespace delta;

namespace {

// Ten ticks of the global clock, with every change of the other signals
// written in a tick's own time slot as F.3.1 assumes, so that the tick a
// SystemVerilog event control fires at is a tick the rewritten Boolean can
// name. clk rises at ticks 1, 5 and 8 and falls at 3 and 6; d rises at 3 and
// falls at 5; the gate en is low from tick 4 to tick 7, which covers the rise
// at 5 and neither other rise; e is triggered at ticks 1 and 6, and the dummy
// bit t is raised with each trigger and lowered at the tick after, so the
// sampled value that next tick reads is 1 as F.3.1's $future_gclk(t) asks.
// Tick 9 changes nothing: a future sampled value function is answered at the
// tick after its own, so the last tick that changes anything needs one more.
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

// A module whose global clocking is gclk's rising edge, with one assertion
// clocked on `control` counting its attempts and one clocked on $global_clock
// counting the ticks at which `rewritten`, the Boolean F.3.1 rewrites
// `control` to, holds.
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

// The attempts of the assertion clocked on `control` and the ticks at which
// `rewritten` holds both number `expected`, which the stimulus makes distinct
// from the counts the other event controls produce.
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

// $global_clock rewrites to 1: the assertion is attempted at every tick.
TEST(ClockControlRewriteSim, GlobalClockIsEveryTick) {
  ExpectRewrite("$global_clock", "1'b1", kTicks);
}

// A bare expression rewrites to $changing_gclk of it: clk changes five times.
TEST(ClockControlRewriteSim, BareExpressionIsChangingGclk) {
  ExpectRewrite("clk", "$changing_gclk(clk)", 5);
}

// posedge rewrites to $rising_gclk: clk rises three times.
TEST(ClockControlRewriteSim, PosedgeIsRisingGclk) {
  ExpectRewrite("posedge clk", "$rising_gclk(clk)", 3);
}

// negedge rewrites to $falling_gclk: clk falls twice.
TEST(ClockControlRewriteSim, NegedgeIsFallingGclk) {
  ExpectRewrite("negedge clk", "$falling_gclk(clk)", 2);
}

// edge rewrites to the disjunction of the posedge and negedge rewrites: clk
// makes five edges.
TEST(ClockControlRewriteSim, EdgeIsRisingOrFallingGclk) {
  ExpectRewrite("edge clk", "$rising_gclk(clk) || $falling_gclk(clk)", 5);
}

// A named event rewrites to $future_gclk of a dummy bit that is 1 in the time
// slots the event is triggered in: e is triggered twice.
TEST(ClockControlRewriteSim, NamedEventIsFutureGclkOfItsDummyBit) {
  ExpectRewrite("e", "$future_gclk(t)", 2);
}

// An iff gate rewrites to a conjunction with the gate: of clk's three rises
// the gate admits two. The gate is a plain operand beside a future sampled
// value function, which this tool reads at the tick after the assertion's, so
// the stimulus holds en steady across the tick after each rise.
TEST(ClockControlRewriteSim, IffIsConjunctionWithTheGate) {
  ExpectRewrite("posedge clk iff en", "$rising_gclk(clk) && en", 2);
}

// `or` rewrites to a disjunction: clk rises three times and d once, at a tick
// clk falls at, so four ticks.
TEST(ClockControlRewriteSim, OrIsDisjunction) {
  ExpectRewrite("posedge clk or posedge d",
                "$rising_gclk(clk) || $rising_gclk(d)", 4);
}

// The comma form rewrites to the same disjunction: clk falls twice and d once,
// at a tick clk rises at, so three ticks.
TEST(ClockControlRewriteSim, CommaIsDisjunction) {
  ExpectRewrite("negedge clk, negedge d",
                "$falling_gclk(clk) || $falling_gclk(d)", 3);
}

}  // namespace
