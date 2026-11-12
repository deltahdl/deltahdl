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

  EXPECT_FALSE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{0}));

  cmgr.MarkBlockEventTime("cb", SimTime{7});
  EXPECT_TRUE(cmgr.DidBlockEventOccurAt("cb", SimTime{7}));
  EXPECT_TRUE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{7}));
  EXPECT_FALSE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{8}));
}

TEST(CycleDelaySim, ZeroDelayEventTimeTracksMostRecentStep) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  cmgr.Register(block);

  cmgr.MarkBlockEventTime("cb", SimTime{4});
  EXPECT_TRUE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{4}));

  cmgr.MarkBlockEventTime("cb", SimTime{9});
  EXPECT_FALSE(cmgr.DidBlockEventOccurAt("cb", SimTime{4}));
  EXPECT_FALSE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{4}));
  EXPECT_TRUE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{9}));

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

  EXPECT_TRUE(cmgr.DidBlockEventOccurAt("cb", SimTime{10}));
  EXPECT_TRUE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{10}));
  EXPECT_FALSE(cmgr.ZeroCycleDelayProceeds("cb", SimTime{5}));
}

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

TEST(CycleDelaySim, AZeroCycleDelayInADriveIsAsIfItWereAbsent) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  logic clk = 0;\n"
                 "  always #10 clk = ~clk;\n"
                 "  logic [7:0] a = 0, b = 0, p = 0, q = 0, s = 0;\n"
                 "  int ta = -1, tb = -1, tp = -1, tq = -1, ts = -1, at = -1;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output a, b, p;\n"
                 "    inout q;\n"
                 "  endclocking\n"
                 "  clocking cs @(posedge clk);\n"
                 "    output #3 s;\n"
                 "  endclocking\n"
                 "  always @(a) ta = $time;\n"
                 "  always @(b) tb = $time;\n"
                 "  always @(p) tp = $time;\n"
                 "  always @(q) tq = $time;\n"
                 "  always @(s) ts = $time;\n"
                 "  initial begin\n"
                 "    @(cb);\n"
                 "    cb.a <= ##0 8'd1;\n"
                 "    cb.b <= 8'd1;\n"
                 "    #1 $display(\"at %0t a@%0d b@%0d\", $time, ta, tb);\n"
                 "    #4;\n"
                 "    cb.a <= ##0 8'd2;\n"
                 "    cb.b <= 8'd2;\n"
                 "    at = $time;\n"
                 "    cb.p[7] <= ##0 1'b1;\n"
                 "    cb.p[3:0] <= ##0 4'hc;\n"
                 "    cb.q <= ##0 8'd5;\n"
                 "    cs.s <= ##0 8'd6;\n"
                 "    $display(\"not held: %0d\", at);\n"
                 "    #20 $display(\"a=%0d@%0d b=%0d@%0d p=%h@%0d q=%0d@%0d "
                 "s=%0d@%0d\", a, ta, b, tb, p, tp, q, tq, s, ts);\n"
                 "    cb.a <= ##0 8'd9;\n"
                 "    cb.b <= ##1 8'd9;\n"
                 "    #40 $display(\"a=%0d@%0d b=%0d@%0d\", a, ta, b, tb);\n"
                 "    $finish;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "at 11 a@10 b@10\nnot held: 15\n"
      "a=2@30 b=2@30 p=8c@30 q=5@30 s=6@33\na=9@50 b=9@70\n"
      "$finish at time 75\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(CycleDelaySim, AnIdentifierOrParenthesizedCountWaitsThatManyEvents) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  always #10 clk = ~clk;\n"
                       "  default clocking cb @(posedge clk); endclocking\n"
                       "  int n = 2, j = 1;\n"
                       "  initial begin\n"
                       "    ##n $display(\"%0t\", $time);\n"
                       "    ##(j + 1) $display(\"%0t\", $time);\n"
                       "    ##1 $display(\"%0t\", $time);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "30\n70\n90\n$finish at time 90\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
