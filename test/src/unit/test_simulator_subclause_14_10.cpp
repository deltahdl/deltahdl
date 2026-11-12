#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

void RegisterClockBlock(ClockingManager& cmgr, const char* name,
                        const char* signal, Edge edge) {
  ClockingBlock block;
  block.name = name;
  block.clock_signal = signal;
  block.clock_edge = edge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);
}

Variable* MakeBlockEvent(ClockingSimFixture& f, ClockingManager& cmgr,
                         const char* var_name, const char* block_name) {
  auto* ev = f.ctx.CreateVariable(var_name, 1);
  ev->is_event = true;
  cmgr.SetBlockEventVar(block_name, ev);
  return ev;
}

void WatchFlag(Variable* ev, bool* flag) {
  ev->AddWatcher([flag]() {
    *flag = true;
    return true;
  });
}

void WatchOrder(Variable* ev, std::vector<std::string>* order,
                const char* label) {
  ev->AddWatcher([order, label]() {
    order->push_back(label);
    return true;
  });
}

Variable* SetupSingleBlockEvent(ClockingSimFixture& f, ClockingManager& cmgr,
                                Edge edge, uint64_t clk_init,
                                Variable** out_event) {
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, clk_init);
  RegisterClockBlock(cmgr, "cb", "clk", edge);
  *out_event = MakeBlockEvent(f, cmgr, "__cb_event", "cb");
  cmgr.Attach(f.ctx, f.scheduler);
  return clk;
}

struct TwoBlockEventSpec {
  const char* sig1;
  const char* sig2;
  bool* fired1;
  bool* fired2;
};

void SetupTwoBlockEvents(ClockingSimFixture& f, ClockingManager& cmgr,
                         const TwoBlockEventSpec& spec) {
  RegisterClockBlock(cmgr, "cb1", spec.sig1, Edge::kPosedge);
  RegisterClockBlock(cmgr, "cb2", spec.sig2, Edge::kPosedge);

  auto* ev1 = MakeBlockEvent(f, cmgr, "__cb1_event", "cb1");
  auto* ev2 = MakeBlockEvent(f, cmgr, "__cb2_event", "cb2");

  cmgr.Attach(f.ctx, f.scheduler);

  WatchFlag(ev1, spec.fired1);
  WatchFlag(ev2, spec.fired2);
}

TEST(ClockingBlockEventSim, EventVarTriggeredOnClockEdge) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  Variable* cb_event = nullptr;
  auto* clk = SetupSingleBlockEvent(f, cmgr, Edge::kPosedge, 0, &cb_event);

  bool triggered = false;
  WatchFlag(cb_event, &triggered);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_TRUE(triggered);
}

TEST(ClockingBlockEventSim, EdgeCallbackInvokedOnPosedge) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  RegisterClockBlock(cmgr, "cb", "clk", Edge::kPosedge);

  uint32_t count = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&count]() { count++; });
  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  ScheduleNegedge(f, clk, 15);
  SchedulePosedge(f, clk, 20);
  f.scheduler.Run();

  EXPECT_EQ(count, 2u);
}

TEST(ClockingBlockEventSim, EventNotTriggeredOnWrongEdge) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  Variable* cb_event = nullptr;
  auto* clk = SetupSingleBlockEvent(f, cmgr, Edge::kPosedge, 0, &cb_event);

  bool triggered = false;
  WatchFlag(cb_event, &triggered);

  ScheduleNegedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_FALSE(triggered);
}

TEST(ClockingBlockEventSim, NegedgeBlockTriggersOnNegedge) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  Variable* cb_event = nullptr;
  auto* clk = SetupSingleBlockEvent(f, cmgr, Edge::kNegedge, 1, &cb_event);

  bool triggered = false;
  WatchFlag(cb_event, &triggered);

  ScheduleNegedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_TRUE(triggered);
}

TEST(ClockingBlockEventSim, AnyEdgeBlockTriggersOnBothEdges) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  Variable* cb_event = nullptr;
  auto* clk = SetupSingleBlockEvent(f, cmgr, Edge::kEdge, 0, &cb_event);

  uint32_t fire_count = 0;
  cb_event->AddWatcher([&fire_count]() {
    ++fire_count;
    return false;
  });

  SchedulePosedge(f, clk, 10);
  ScheduleNegedge(f, clk, 20);
  f.scheduler.Run();

  EXPECT_EQ(fire_count, 2u);
}

TEST(ClockingBlockEventSim, MultipleBlocksTriggerIndependentEvents) {
  ClockingSimFixture f;
  auto* clk1 = f.ctx.CreateVariable("clk1", 1);
  clk1->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* clk2 = f.ctx.CreateVariable("clk2", 1);
  clk2->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  bool ev1_fired = false;
  bool ev2_fired = false;
  SetupTwoBlockEvents(
      f, cmgr, TwoBlockEventSpec{"clk1", "clk2", &ev1_fired, &ev2_fired});

  SchedulePosedge(f, clk1, 10);
  f.scheduler.Run();

  EXPECT_TRUE(ev1_fired);
  EXPECT_FALSE(ev2_fired);
}

TEST(ClockingBlockEventSim, NamedEventFiresInObservedRegionAfterActiveAndNBA) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  Variable* cb_event = nullptr;
  auto* clk = SetupSingleBlockEvent(f, cmgr, Edge::kPosedge, 0, &cb_event);

  std::vector<std::string> order;
  WatchOrder(cb_event, &order, "block_event");

  auto* active_ev = f.scheduler.GetEventPool().Acquire();
  active_ev->callback = [&order]() { order.push_back("active"); };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, active_ev);

  auto* nba_ev = f.scheduler.GetEventPool().Acquire();
  nba_ev->callback = [&order]() { order.push_back("nba"); };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kNBA, nba_ev);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "nba");
  EXPECT_EQ(order[2], "block_event");
}

TEST(ClockingBlockEventSim, MultipleWatchersAllFireOnEdge) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  Variable* cb_event = nullptr;
  auto* clk = SetupSingleBlockEvent(f, cmgr, Edge::kPosedge, 0, &cb_event);

  bool watcher_a = false;
  bool watcher_b = false;
  WatchFlag(cb_event, &watcher_a);
  WatchFlag(cb_event, &watcher_b);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_TRUE(watcher_a);
  EXPECT_TRUE(watcher_b);
}

TEST(ClockingBlockEventSim, SharedClockBothBlocksFireEvents) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  bool ev1_fired = false;
  bool ev2_fired = false;
  SetupTwoBlockEvents(f, cmgr,
                      TwoBlockEventSpec{"clk", "clk", &ev1_fired, &ev2_fired});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_TRUE(ev1_fired);
  EXPECT_TRUE(ev2_fired);
}

void ScheduleClockValue(ClockingSimFixture& f, Variable* clk, uint64_t value,
                        uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, value, &f]() {
    clk->value = MakeLogic4VecVal(f.arena, 1, value);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

TEST(ClockingEventSim, PosedgeBlockFiresOncePerPosedgeOnAnUnwatchedClock) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  RegisterClockBlock(cmgr, "cb", "clk", Edge::kPosedge);
  cmgr.Attach(f.ctx, f.scheduler);

  int fired = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&fired]() { ++fired; });

  ScheduleClockValue(f, clk, 1, 10);
  ScheduleClockValue(f, clk, 0, 20);
  ScheduleClockValue(f, clk, 1, 30);
  f.scheduler.Run();

  EXPECT_EQ(fired, 2);
}

TEST(ClockingEventSim, NegedgeBlockFiresOnTheFallOfAnUnwatchedClock) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  RegisterClockBlock(cmgr, "cb", "clk", Edge::kNegedge);
  cmgr.Attach(f.ctx, f.scheduler);

  int fired = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&fired]() { ++fired; });

  ScheduleClockValue(f, clk, 1, 10);
  ScheduleClockValue(f, clk, 0, 20);
  f.scheduler.Run();

  EXPECT_EQ(fired, 1);
}

TEST(ClockingBlockEventSim, ClockingBlockEventFromSourceTriggersOnTheEdge) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic [7:0] data = 8'h00;\n"
      "  int hits = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  always @(cb) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
}

TEST(ClockingBlockEventSim, ClockingBlockEventFollowsTheDeclaredEdge) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic [7:0] data = 8'h00;\n"
      "  int hits = 0;\n"
      "  clocking cb @(negedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  always @(cb) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

TEST(ClockingBlockEventSim, ClockingManagerIsInstalledForADesignWithABlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic [7:0] data = 8'h00;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial #5 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_NE(f.ctx.GetClockingManager(), nullptr);
  EXPECT_EQ(f.ctx.GetClockingManager()->Count(), 1u);
  EXPECT_NE(f.ctx.GetClockingManager()->Find("cb"), nullptr);
}

TEST(ClockingBlockEventSim, AChildInstancesBlockTriggersItsOwnEvent) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module leaf(input logic clk);\n"
      "  logic [7:0] data = 8'h00;\n"
      "  int hits = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  always @(cb) hits = hits + 1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 1'b0;\n"
      "  leaf u(.clk(clk));\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    #5 clk = 1'b0;\n"
      "    #5 clk = 1'b1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "u.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
}

TEST(ClockingBlockEventSim, NamedEventClocksTheBlock) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  event e;\n"
      "  logic [7:0] d = 1;\n"
      "  clocking cb @(e);\n"
      "    input d;\n"
      "  endclocking\n"
      "  initial begin #2 d = 2; #2 -> e; #1 d = 3; #4 -> e; end\n"
      "  initial begin\n"
      "    @(cb); $write(\"%0t:%0d \", $time, cb.d);\n"
      "    @(cb); $display(\"%0t:%0d\", $time, cb.d);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4:2 9:3\n$finish at time 9\n");
}

TEST(ClockingBlockEventSim,
     TheClauseExampleBlockEventRunsAfterTheEdgesUpdates) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module foo(input phi1, input [7:0] data);\n"
          "  logic [7:0] address;\n"
          "  int v = 0, w = 0;\n"
          "  clocking dram @(posedge phi1);\n"
          "    input data;\n"
          "    output negedge #1 address;\n"
          "  endclocking\n"
          "  always @(posedge phi1) $display(\"clocking event %0d %0d\", v, "
          "w);\n"
          "  always @(dram) $display(\"clocking block event %0d %0d\", v, w);\n"
          "  always @(posedge phi1) v <= v + 1;\n"
          "  always @(posedge phi1) #0 w = w + 1;\n"
          "endmodule\n"
          "module top;\n"
          "  logic phi1 = 0;\n"
          "  logic [7:0] data = 3;\n"
          "  foo f(phi1, data);\n"
          "  initial begin #5 phi1 = 1; #5 phi1 = 0; #5 phi1 = 1; #1 $finish; "
          "end\n"
          "endmodule\n",
          f),
      "clocking event 0 0\nclocking block event 1 1\nclocking event 1 1\n"
      "clocking block event 2 2\n$finish at time 16\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
