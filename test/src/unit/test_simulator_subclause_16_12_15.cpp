#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The module the cases share: clk rises at 5, 15 and 25 and stops, the run
// going on to 100 with no further tick, the tick counter counting through
// so that tick n is at 10n - 5; a is high throughout, b low throughout and
// c high at ticks 1 and 2 alone. `items` declare the assertions, counting
// in `passes` and `fails`, and `when` records the time of the last fail.
std::string WeakStrongSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a = 1, b = 0, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int when = 0;\n"
         "  initial repeat (6) #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign c = tick inside {1, 2};\n" +
         items +
         "  initial #100 $finish;\n"
         "endmodule\n";
}

// The fail count of an assertion whose property is `spec`, after the run
// and its final blocks, where the verdicts on the attempts in flight when
// the run ends are reached.
uint64_t FailsOf(const std::string& spec) {
  SimFixture f;
  auto* fails = RunAndFindVar(
      WeakStrongSource("  p: assert property (@(posedge clk) " + spec +
                       ") passes++; else begin fails++; when = $time; end\n"),
      f, "fails");
  if (fails == nullptr) return ~0ull;
  f.ctx.RunFinalBlocks();
  return fails->value.ToUint64();
}

// §16.12.15: nexttime imposes no requirement that the clock tick again, so
// the attempt from the last tick holds when the run ends, where s_nexttime
// requires the next tick and fails there.
TEST(WeakStrongOperators, NexttimeNeedsNoTickWhereSNexttimeDoes) {
  EXPECT_EQ(FailsOf("nexttime a"), 0u);
  EXPECT_EQ(FailsOf("s_nexttime a"), 1u);
}

// §16.12.15: always and a ranged eventually hold when the clock stops with
// their ranges unfinished, where s_always over a range and s_eventually
// require the ticks and the condition, and fail every attempt at the end.
TEST(WeakStrongOperators, AlwaysAndEventuallyHoldWhereTheStrongFormsFail) {
  EXPECT_EQ(FailsOf("always a"), 0u);
  EXPECT_EQ(FailsOf("s_always [0:3] a"), 3u);
  EXPECT_EQ(FailsOf("eventually [0:3] b"), 0u);
  EXPECT_EQ(FailsOf("s_eventually b"), 3u);
}

// §16.12.15: until and the weak sequence operator hold with their
// terminating condition unmet when the clock stops, where s_until and
// strong fail.
TEST(WeakStrongOperators, UntilAndWeakHoldWhereSUntilAndStrongFail) {
  EXPECT_EQ(FailsOf("a until b"), 0u);
  EXPECT_EQ(FailsOf("a s_until b"), 3u);
  EXPECT_EQ(FailsOf("weak(a ##1 a)"), 0u);
  EXPECT_EQ(FailsOf("strong(a ##1 a)"), 1u);
}

// §16.12.15: `always c` is a safety property, its failures happening at a
// finite time: the three attempts fail at 25, the tick c falls at, with the
// clock still ticking, rather than when the run ends.
TEST(WeakStrongOperators, ASafetyPropertyFailsAtAFiniteTime) {
  SimFixture f;
  auto* fails = RunAndFindVar(
      WeakStrongSource("  p: assert property (@(posedge clk) always c) "
                       "passes++; else begin fails++; when = $time; end\n"),
      f, "fails");
  ASSERT_NE(fails, nullptr);
  EXPECT_EQ(fails->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("when")->value.ToUint64(), 25u);
}

}  // namespace
