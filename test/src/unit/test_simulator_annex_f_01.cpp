#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

// Annex F.1: general.
//
// F.1 gives the annex its subject, the concurrent assertions, and keeps the
// immediate assertions and the coverage statements out of it. F.2 then
// defines the semantics as a relation between a word, a sequence of the
// design's variables as sampled, and an assertion. What that scope line means
// at a run is that a concurrent assertion's verdict is one over sampled
// values, while an immediate assertion's is over the value its condition has
// where the statement executes (§16.3), so the two can differ on the same
// variable at the same clock tick, and only the concurrent one is the annex's.

using namespace delta;

namespace {

// A design where `a` rises in the time step of the tick, after the tick's
// Preponed region and before the immediate assertions execute. Each assertion
// counts its passes in a variable of its own: `sampled` for the concurrent
// assert property, `live` for a simple immediate assertion (§16.3) in a
// procedure the same tick wakes, and `deferred` for the observed deferred
// immediate assertion of §16.4, whose condition is read where the statement
// executes as the simple one's is. The rise and the tick stand in one time
// step, which is what tells a sampled read from a live one.
constexpr const char* kOneTick =
    "module m;\n"
    "  logic clk = 0;\n"
    "  logic a = 0;\n"
    "  int sampled = 0;\n"
    "  int live = 0;\n"
    "  int deferred = 0;\n"
    "  assert property (@(posedge clk) a) sampled = sampled + 1;\n"
    "  always @(posedge clk) assert (a) live = live + 1;\n"
    "  always @(posedge clk) assert #0 (a) deferred = deferred + 1;\n"
    "  initial begin\n"
    "    #5 a = 1;\n"
    "    clk = 1;\n"
    "  end\n"
    "endmodule\n";

// The concurrent assertion is the annex's: its verdict is over the word, and
// the letter for the tick's time slot carries the 0 that `a` had in the
// Preponed region, so the assertion does not hold and counts no pass.
TEST(FormalSemanticsGeneral, AConcurrentAssertionIsJudgedOnTheSampledWord) {
  SimFixture f;
  auto* sampled = RunAndFindVar(kOneTick, f, "sampled");
  ASSERT_NE(sampled, nullptr);
  EXPECT_EQ(sampled->value.ToUint64(), 0u);
}

// The simple immediate assertion is outside the annex: it reads `a` where it
// executes, after the rise, and passes at the tick the concurrent assertion
// fails.
TEST(FormalSemanticsGeneral, ASimpleImmediateAssertionIsJudgedOnTheLiveValue) {
  SimFixture f;
  auto* live = RunAndFindVar(kOneTick, f, "live");
  ASSERT_NE(live, nullptr);
  EXPECT_EQ(live->value.ToUint64(), 1u);
}

// The deferred immediate assertion is an immediate assertion too, §16.4
// deferring only its action block, so it is outside the annex with the simple
// one and reads the same live 1.
TEST(FormalSemanticsGeneral,
     ADeferredImmediateAssertionIsJudgedOnTheLiveValue) {
  SimFixture f;
  auto* deferred = RunAndFindVar(kOneTick, f, "deferred");
  ASSERT_NE(deferred, nullptr);
  EXPECT_EQ(deferred->value.ToUint64(), 1u);
}

// The control: with `a` settled a time step before the tick, the letter and
// the live value agree, and all three assertions pass. Without it a
// concurrent assertion that never passes satisfies the first case.
TEST(FormalSemanticsGeneral, TheThreeAgreeWhenTheValueSettledBeforeTheTick) {
  SimFixture f;
  const std::string kSettled =
      "module m;\n"
      "  logic clk = 0;\n"
      "  logic a = 0;\n"
      "  int sampled = 0;\n"
      "  int live = 0;\n"
      "  int deferred = 0;\n"
      "  assert property (@(posedge clk) a) sampled = sampled + 1;\n"
      "  always @(posedge clk) assert (a) live = live + 1;\n"
      "  always @(posedge clk) assert #0 (a) deferred = deferred + 1;\n"
      "  initial begin\n"
      "    #5 a = 1;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n";
  auto* sampled = RunAndFindVar(kSettled, f, "sampled");
  ASSERT_NE(sampled, nullptr);
  EXPECT_EQ(sampled->value.ToUint64(), 1u);
  auto* live = f.ctx.FindVariable("live");
  ASSERT_NE(live, nullptr);
  EXPECT_EQ(live->value.ToUint64(), 1u);
  auto* deferred = f.ctx.FindVariable("deferred");
  ASSERT_NE(deferred, nullptr);
  EXPECT_EQ(deferred->value.ToUint64(), 1u);
}

}  // namespace
