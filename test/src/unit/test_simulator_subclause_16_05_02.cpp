#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"

// §16.5.2 "Assertion clock".
//
// The clause fixes what clocks a concurrent assertion. Three of its statements
// are observable on real source driven through the simulator, and each test
// below observes one of them:
//
//   - the clock "can vary from one expression to another", so two assertions in
//     one module are checked at the ticks of their own clocks and at no others;
//   - "clk iff gating_signal" represents a gated clock, so a tick whose gate is
//     false starts no evaluation attempt;
//   - "assert property(@$global_clock a);" under a "global clocking @clk;
//     endclocking" declaration "is logically equivalent to
//     assert property(@clk a);", so the assertion is checked at that
//     declaration's event.
//
// Each test counts the pass actions a static concurrent assertion runs
// (§16.14.5 gives it `always` semantics, one fresh attempt per leading clock),
// so the count names the ticks the assertion was clocked at.

using namespace delta;

namespace {

// §16.5.2: the assertion clock "can vary from one expression to another". Two
// assertions stand in one module on two different clocks, and the run drives
// three posedges of the first and two of the second. Each counter reaches its
// own clock's tally rather than the total of five, so neither assertion was
// checked at the other's ticks. The two counts differ, so an implementation
// that clocked both assertions off whichever edge occurred fails whichever
// count it did not produce.
TEST(AssertionClockSim, ClockVariesFromOneAssertionToAnother) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk1;\n"
      "  logic clk2;\n"
      "  int hits1 = 0;\n"
      "  int hits2 = 0;\n"
      "  assert property (@(posedge clk1) 1'b1) hits1 = hits1 + 1;\n"
      "  assert property (@(posedge clk2) 1'b1) hits2 = hits2 + 1;\n"
      "  initial begin\n"
      "    clk1 = 0;\n"
      "    clk2 = 0;\n"
      "    #5 clk1 = 1;\n"  // clk1 tick 1
      "    #5 clk1 = 0;\n"
      "    #5 clk2 = 1;\n"  // clk2 tick 1
      "    #5 clk1 = 1;\n"  // clk1 tick 2
      "    #5 clk1 = 0;\n"
      "    #5 clk2 = 0;\n"
      "    #5 clk2 = 1;\n"  // clk2 tick 2
      "    #5 clk1 = 1;\n"  // clk1 tick 3
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* hits1 = f.ctx.FindVariable("hits1");
  ASSERT_NE(hits1, nullptr);
  EXPECT_EQ(hits1->value.ToUint64(), 3u);
  auto* hits2 = f.ctx.FindVariable("hits2");
  ASSERT_NE(hits2, nullptr);
  EXPECT_EQ(hits2->value.ToUint64(), 2u);
}

// §16.5.2: "clk iff gating_signal" represents a gated clock. Four posedges of
// clk occur and the gate is high at two of them, so the assertion runs two
// evaluation attempts. A gate that was ignored would give four, and a gate that
// suppressed the clock outright would give none.
TEST(AssertionClockSim, GatedClockSkipsTheTicksItsGateSuppresses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic en;\n"
      "  int hits = 0;\n"
      "  assert property (@(posedge clk iff en) 1'b1) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    en = 1;\n"
      "    #5 clk = 1;\n"  // tick 1, gate high -> attempt
      "    #5 clk = 0;\n"
      "    #5 en = 0;\n"
      "    #5 clk = 1;\n"  // tick 2, gate low -> no attempt
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"  // tick 3, gate low -> no attempt
      "    #5 clk = 0;\n"
      "    #5 en = 1;\n"
      "    #5 clk = 1;\n"  // tick 4, gate high -> attempt
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §16.5.2: an assertion whose leading clocking event is $global_clock is
// clocked by the event of the global clocking declaration, the clause's
// equivalence between `assert property(@$global_clock a);` and
// `assert property(@clk a);`. Three posedges of clk occur, so the assertion
// runs three attempts. An implementation that left $global_clock standing for
// no event at all would give none.
TEST(AssertionClockSim, GlobalClockClocksTheAssertionAtTheGlobalClockingEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "  assert property (@$global_clock 1'b1) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"  // tick 1
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"  // tick 2
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"  // tick 3
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §16.5.2: the equivalence names the declared event, not an edge chosen for it.
// The global clocking here is on the negedge, and the run drives three negedges
// and two posedges of the same signal. The assertion runs three attempts, so it
// followed the declared edge; an implementation that read $global_clock as the
// posedge of the global clock would give two.
TEST(AssertionClockSim, GlobalClockFollowsTheDeclaredEdge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  int hits = 0;\n"
      "  global clocking gclk @(negedge clk); endclocking\n"
      "  assert property (@$global_clock 1'b1) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 1;\n"
      "    #5 clk = 0;\n"  // negedge 1
      "    #5 clk = 1;\n"  // posedge 1
      "    #5 clk = 0;\n"  // negedge 2
      "    #5 clk = 1;\n"  // posedge 2
      "    #5 clk = 0;\n"  // negedge 3
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

}  // namespace
