#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"

// §16.14.5 "Using concurrent assertion statements outside procedural code".
//
// A concurrent assertion statement written directly in a module (outside any
// procedure) uses `always` semantics: a fresh evaluation attempt of the
// underlying property begins at every occurrence of its leading clock event,
// so the assertion is checked from the beginning to the end of simulation.
//
// The elaborator carries this rule for the simple clocked form. It captures the
// leading clock in item->sensitivity and wraps the boolean as an immediate
// assert in item->body (parser_assert.cpp), then models the module-item
// assertion as a clocked process (elaborator_items.cpp, kAlwaysFF). At run time
// the lowerer spawns a sensitized clocked coroutine that re-runs the assert
// body -- and its action block -- at each leading clock edge (lowerer.cpp).
//
// These tests observe the rule end-to-end. The source contains no procedure
// wrapping the assertion; the only reason its action block executes at all, and
// executes once per leading clock, is the §16.14.5 always semantics. The input
// is built from real module-level source and driven through
// parse/elaborate/lower/run, so the live simulator applies the rule rather than
// a hand-built process or a synthetic helper.

using namespace delta;

namespace {

// A static concurrent assert whose boolean always holds fires its pass action
// once for every leading clock edge over the whole run. Three posedge events
// occur, so the counter reaches 3: a fresh evaluation attempt began at each
// leading clock, exactly the `always` semantics §16.14.5 assigns to a
// concurrent assertion used outside procedural code.
TEST(StaticConcurrentAssertionSim, StartsFreshAttemptAtEachLeadingClock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  int hits = 0;\n"
      "  assert property (@(posedge clk) 1'b1) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"  // posedge 1 -> attempt 1
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"  // posedge 2 -> attempt 2
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"  // posedge 3 -> attempt 3
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

// Each leading clock starts an independent evaluation attempt of the current
// property value, not a single persistent check. The condition is high for the
// first and third posedge and low for the second, so the pass action runs
// exactly twice. Observing hits==2 (out of three leading clocks) shows the
// assertion re-evaluates afresh at every clock edge rather than latching a
// single result -- the per-clock attempt behaviour of §16.14.5.
TEST(StaticConcurrentAssertionSim, ReevaluatesConditionOnEachLeadingClock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic cond;\n"
      "  int hits = 0;\n"
      "  assert property (@(posedge clk) cond) hits = hits + 1;\n"
      "  initial begin\n"
      "    clk = 0; cond = 1;\n"
      "    #5 clk = 1;\n"  // posedge 1: cond=1 -> pass
      "    #5 clk = 0; cond = 0;\n"
      "    #5 clk = 1;\n"  // posedge 2: cond=0 -> no pass action
      "    #5 clk = 0; cond = 1;\n"
      "    #5 clk = 1;\n"  // posedge 3: cond=1 -> pass
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

}  // namespace
