#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_scheduler.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CycleDelaySim, EdgeCallbackCountsThreeEdges) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  cmgr.SetDefaultClocking("cb");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "cb");

  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);
  ScheduleNegedge(f, clk, 15);
  SchedulePosedge(f, clk, 20);
  ScheduleNegedge(f, clk, 25);
  SchedulePosedge(f, clk, 30);

  uint32_t edge_count = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler,
                            [&edge_count]() { edge_count++; });

  cmgr.Attach(f.ctx, f.scheduler);
  f.scheduler.Run();
  EXPECT_GE(edge_count, 3u);
}

TEST(CycleDelaySim, DefaultClockingRegistered) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "bus";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  cmgr.Register(block);

  cmgr.SetDefaultClocking("bus");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "bus");
  EXPECT_NE(cmgr.Find("bus"), nullptr);
}

TEST(CycleDelaySim, ZeroDelaySuspendsUntilEventThenProceeds) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  cmgr.Register(block);

  // §14.11: with no clocking block event yet in the current time step, a ##0
  // cycle delay must suspend the calling process.
  EXPECT_FALSE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{0}));

  // Once the event has occurred in the current step, a ##0 continues without
  // suspension at that step...
  cmgr.MarkBlockEventTime("cb", SimTime{7});
  EXPECT_TRUE(cmgr.DidBlockEventOccurAt("cb", SimTime{7}));
  EXPECT_TRUE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{7}));
  // ...but a later time step has not yet seen its own clocking event.
  EXPECT_FALSE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{8}));
}

TEST(CycleDelaySim, ZeroDelayEventTimeTracksMostRecentStep) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  cmgr.Register(block);

  // §14.11: a ##0 continues only at the exact step whose clocking event fired.
  cmgr.MarkBlockEventTime("cb", SimTime{4});
  EXPECT_TRUE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{4}));

  // A later clocking event advances the recorded step; the earlier step no
  // longer counts as having a coincident event, so a ##0 there would suspend.
  cmgr.MarkBlockEventTime("cb", SimTime{9});
  EXPECT_FALSE(cmgr.DidBlockEventOccurAt("cb", SimTime{4}));
  EXPECT_FALSE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{4}));
  EXPECT_TRUE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{9}));

  // A block that has never seen an event has no coincident step at all.
  EXPECT_FALSE(cmgr.ZeroCycleDelayProceeds("absent", SimTime{9}));
}

TEST(CycleDelaySim, ZeroDelayEventTimeRecordedFromClockWatcher) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);
  cmgr.SetDefaultClocking("cb");
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);
  cmgr.Attach(f.ctx, f.scheduler);
  f.scheduler.Run();

  // The clocking block event fired at time 10, so a ##0 evaluated at that step
  // proceeds, while one evaluated at an earlier step would have suspended.
  EXPECT_TRUE(cmgr.DidBlockEventOccurAt("cb", SimTime{10}));
  EXPECT_TRUE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{10}));
  EXPECT_FALSE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{5}));
}

// §14.11 with §8.6: a class task resumed from a cycle delay still runs on the
// object it was called on, so the property written after `##2` is that
// object's.
TEST(CycleDelaySim, ClassTaskResumedFromACycleDelayWritesItsObject) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic clk = 0;\n"
      "  default clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  class C;\n"
      "    int v;\n"
      "    task run; ##2; v = 3; endtask\n"
      "  endclass\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C h = new;\n"
      "    #4 h.run();\n"
      "    result = h.v * 100 + $time;\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 315u);
}

// §14.11 (printed page 361) with §9.2 and §9.3.2: a cycle delay is a blocking
// wait like any other, so a process may take any number of them in sequence,
// in a loop or in parallel fork branches and run on. A resumed process
// registered its next wait while the waits were being called, which grew the
// table under the loop, and a wait kept after it resumed counted on freed
// memory: each of these crashed the run or stopped it short.
TEST(CycleDelaySim, SequentialLoopedAndForkedCycleDelaysRunOn) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int n = 0;\n"
      "  default clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  always begin ##2; n++; end\n"
      "  task automatic both(); fork ##1; ##3; join endtask\n"
      "  initial begin\n"
      "    ##1; $write(\"%0t \", $time);\n"
      "    ##1; $write(\"%0t \", $time);\n"
      "    #2 ##1; $write(\"%0t \", $time);\n"
      "    both(); $write(\"%0t \", $time);\n"
      "    #2 $display(\"n=%0d\", n);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 15 25 55 n=3\n$finish at time 57\n");
}

// §14.11: `##N` waits for N clocking block events, and one executed in the
// time step of an event -- after `@(cb)`, after the edge's own `@(posedge
// clk)`, or straight after another cycle delay resumed by that event -- waits
// a full cycle for the first of them. Each counted the event of its own time
// step and returned a cycle early: 5, 5 and 25 in place of 15, 15 and 35.
TEST(CycleDelaySim, CycleDelayDoesNotCountTheEventOfItsOwnTimeStep) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  default clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin @(cb); ##1; $write(\"%0t \", $time); end\n"
      "  initial begin @(posedge clk); ##1; $write(\"%0t \", $time); end\n"
      "  initial begin\n"
      "    #40 ##2; $write(\"%0t \", $time);\n"
      "    ##2; $display(\"%0t\", $time);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "15 15 55 75\n$finish at time 75\n");
}

// §14.11 (printed page 361): `##0` suspends until the clocking block event
// when that event has not yet occurred in the current time step and runs on
// when it has, and `##(n)` with n at 0 is the same wait. So the first `##0`
// waits for the edge at 5, the second, in that step, does not, and one at 7
// waits for 15. A zero count was skipped, and each ran on at once: 0, 0, 7.
TEST(CycleDelaySim, ZeroCycleDelayWaitsForTheEventOfItsStep) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  int n = 0;\n"
      "  default clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin\n"
      "    ##0; $write(\"%0t \", $time);\n"
      "    ##(n); $write(\"%0t \", $time);\n"
      "    #2 ##0; $display(\"%0t\", $time);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 5 15\n$finish at time 15\n");
}

}  // namespace
