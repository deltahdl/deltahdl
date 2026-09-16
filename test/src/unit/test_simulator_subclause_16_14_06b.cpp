#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"

using namespace delta;

namespace {

// A module around the procedures given, as
// test/src/e2e/procedural_concurrent_assertions.sv is: mclk rises at 10,
// 30, ..., 110, scanclk at 20, 60 and 100, fastclk at 5, 15, ..., 115 and
// clock at 15, 45, 75 and 105; d is 1 throughout, d1 is 1 from 25 to 65,
// reset is high from 40 to 50 and d2 is 1; the clause's r1 is q != d and
// r2 is q2 != d2; the run ends at 120.
std::string ProceduralSource(const std::string& procedures) {
  return "module t;\n"
         "  logic mclk = 0, scanclk = 0, fastclk = 0, clock = 0;\n"
         "  logic reset = 0;\n"
         "  logic d1 = 0, d = 1, q = 0;\n"
         "  logic d2 = 1, q2 = 0;\n"
         "  int cnt = 0;\n"
         "  int passes = 0, fails = 0, hits = 0;\n"
         "  always #10 mclk = ~mclk;\n"
         "  always #20 scanclk = ~scanclk;\n"
         "  always #5 fastclk = ~fastclk;\n"
         "  always #15 clock = ~clock;\n"
         "  property r1;\n"
         "    q != d;\n"
         "  endproperty\n"
         "  property r2;\n"
         "    q2 != d2;\n"
         "  endproperty\n" +
         procedures +
         "  initial begin\n"
         "    #25 d1 = 1;\n"
         "    #15 reset = 1;\n"
         "    #10 reset = 0;\n"
         "    #15 d1 = 0;\n"
         "    #55 $finish;\n"
         "  end\n"
         "endmodule\n";
}

uint64_t Count(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? 0 : var->value.ToUint64();
}

// §16.14.6: the clause's r1_p1 takes the clock inferred from the procedure,
// posedge mclk, its instance queued at each posedge maturing in the
// Observed region of the same step, where the event occurred, so it is
// evaluated at every posedge of mclk on the sampled q: 1 across the ticks
// of 50 and 70, where it fails, and 0 at the four others.
TEST(ProceduralConcurrentAssertionRun, AnInferredClockEvaluatesAtItsOwnTick) {
  SimFixture f;
  RunAndFindVar(ProceduralSource("  always @(posedge mclk) begin\n"
                                 "    q <= d1;\n"
                                 "    r1_p1: assert property (r1) passes++;\n"
                                 "    else fails++;\n"
                                 "  end\n"),
                f, "passes");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(Count(f, "passes"), 4u);
  EXPECT_EQ(Count(f, "fails"), 2u);
}

// §16.14.6: the clause's r1_p2 is clocked by scanclk as written, and mclk
// runs at twice its frequency, so by every posedge of scanclk two pending
// instances have matured and each posedge sees r1_p2 evaluated twice: the
// instance of 10 at 20, those of 30 and 50 at 60, both failing, and those
// of 70 and 90 at 100, the instance of 110 still waiting at the end.
TEST(ProceduralConcurrentAssertionRun,
     ASlowerOwnClockEvaluatesEveryMaturedInstanceAtItsNextTick) {
  SimFixture f;
  std::string out = RunCapture(
      ProceduralSource("  always @(posedge mclk) begin\n"
                       "    q <= d1;\n"
                       "    r1_p2: assert property (@(posedge scanclk) r1)\n"
                       "      $display(\"passed at %0d\", $time);\n"
                       "    else $display(\"failed at %0d\", $time);\n"
                       "  end\n"),
      f);
  EXPECT_EQ(out,
            "passed at 20\nfailed at 60\nfailed at 60\npassed at 100\n"
            "passed at 100\n$finish at time 120\n");
}

// §16.14.6: the clause's r1_p3 is clocked by fastclk, which runs at twice
// the frequency of mclk, so only every other posedge of fastclk evaluates
// it, the instance queued at each posedge of mclk at the posedge of fastclk
// after it.
TEST(ProceduralConcurrentAssertionRun,
     AFasterOwnClockEvaluatesOnlyAtTheTicksAfterAnInstanceWasQueued) {
  SimFixture f;
  std::string out = RunCapture(
      ProceduralSource("  always @(posedge mclk) begin\n"
                       "    q <= d1;\n"
                       "    r1_p3: assert property (@(posedge fastclk) r1)\n"
                       "      $display(\"passed at %0d\", $time);\n"
                       "    else $display(\"failed at %0d\", $time);\n"
                       "  end\n"),
      f);
  EXPECT_EQ(out,
            "passed at 15\nfailed at 35\nfailed at 55\npassed at 75\n"
            "passed at 95\npassed at 115\n$finish at time 120\n");
}

// §16.14.6: a statement a loop reaches three times in one time step places
// three pending instances in the queue, and each begins an attempt at the
// tick, so r1 is evaluated three times at every posedge of mclk.
TEST(ProceduralConcurrentAssertionRun, EachReachInAStepQueuesAnInstance) {
  SimFixture f;
  RunAndFindVar(
      ProceduralSource("  always @(posedge mclk) begin\n"
                       "    q <= d1;\n"
                       "    for (int i = 0; i < 3; i++)\n"
                       "      loop_p: assert property (r1) passes++;\n"
                       "      else fails++;\n"
                       "  end\n"),
      f, "passes");
  EXPECT_EQ(Count(f, "passes"), 12u);
  EXPECT_EQ(Count(f, "fails"), 6u);
}

// §16.14.6: the clause's r2_p under posedge clock iff reset == 0 or posedge
// reset takes the inferred clock posedge clock iff reset == 0, reset being
// referenced in the procedure: the instance queued at 40, when reset rose,
// finds no occurrence of that event in its step and waits on the matured
// queue, the event of 45 not occurring while reset is high, so two
// instances are evaluated at 75 and one at 105, each failing, q2 having
// taken d2 at 15, where the one instance passed.
TEST(ProceduralConcurrentAssertionRun,
     AnInstanceWhoseClockDidNotOccurWaitsForItsNextTick) {
  SimFixture f;
  std::string out = RunCapture(
      ProceduralSource(
          "  always_ff @(posedge clock iff reset == 0 or posedge reset)\n"
          "  begin\n"
          "    cnt <= reset ? 0 : cnt + 1;\n"
          "    q2 <= d2;\n"
          "    r2_p: assert property (r2) $display(\"passed at %0d\", $time);\n"
          "    else $display(\"failed at %0d\", $time);\n"
          "  end\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "passed at 15\nfailed at 75\nfailed at 75\nfailed at 105\n"
            "$finish at time 120\n");
}

// §16.14.6: an initial procedure holding a delay gives no inferred clock,
// so the clocks are inferred from the default clocking, posedge scanclk, as
// if the assertion were instantiated before the procedure: the instance
// queued at 12 is evaluated at 20, where r1 holds.
TEST(ProceduralConcurrentAssertionRun,
     TheDefaultClockingClocksWhatNoContextDoes) {
  SimFixture f;
  RunAndFindVar(ProceduralSource(
                    "  default clocking dc @(posedge scanclk); endclocking\n"
                    "  initial begin\n"
                    "    #12;\n"
                    "    r4_p: assert property (r1) passes++; else fails++;\n"
                    "  end\n"),
                f, "passes");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(Count(f, "passes"), 1u);
  EXPECT_EQ(Count(f, "fails"), 0u);
}

// §16.14.6: a cover statement embedded in procedural code is queued and
// evaluated as an assert is, its results counted under the statement's
// label, and a temporal property embedded there advances over the ticks
// of its inferred clock after the instance matured: q rises the tick after
// d1 does, so d1 |=> q holds at 50 and fails nowhere, its attempts of 30
// and 50 in flight across a tick each.
TEST(ProceduralConcurrentAssertionRun,
     ACoverAndATemporalPropertyAreQueuedAndEvaluated) {
  SimFixture f;
  RunAndFindVar(
      ProceduralSource("  always @(posedge mclk) begin\n"
                       "    q <= d1;\n"
                       "    c_p: cover property (q == d1) hits++;\n"
                       "    t_p: assert property (d1 |=> q) passes++;\n"
                       "    else fails++;\n"
                       "  end\n"),
      f, "hits");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(Count(f, "hits"), 4u);
  const auto& results = f.ctx.ConcurrentCovers().Results();
  ASSERT_EQ(results.size(), 1u);
  EXPECT_EQ(results[0].scope, "t.c_p");
  EXPECT_EQ(results[0].attempted, 6u);
  EXPECT_EQ(results[0].succeeded, 4u);
  EXPECT_EQ(Count(f, "passes"), 6u);
  EXPECT_EQ(Count(f, "fails"), 0u);
}

}  // namespace
