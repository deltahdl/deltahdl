#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ClockingBlockEventSim, EventVarTriggeredOnClockEdge) {
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

  auto* cb_event = f.ctx.CreateVariable("__cb_event", 1);
  cb_event->is_event = true;
  cmgr.SetBlockEventVar("cb", cb_event);

  cmgr.Attach(f.ctx, f.scheduler);

  bool triggered = false;
  cb_event->AddWatcher([&triggered]() {
    triggered = true;
    return true;
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_TRUE(triggered);
}

TEST(ClockingBlockEventSim, EdgeCallbackInvokedOnPosedge) {
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

  auto* cb_event = f.ctx.CreateVariable("__cb_event", 1);
  cb_event->is_event = true;
  cmgr.SetBlockEventVar("cb", cb_event);

  cmgr.Attach(f.ctx, f.scheduler);

  bool triggered = false;
  cb_event->AddWatcher([&triggered]() {
    triggered = true;
    return true;
  });

  ScheduleNegedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_FALSE(triggered);
}

TEST(ClockingBlockEventSim, EventFiresInObservedRegion) {
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

  std::vector<std::string> order;

  auto* active_ev = f.scheduler.GetEventPool().Acquire();
  active_ev->callback = [&order]() { order.push_back("active"); };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, active_ev);

  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler,
                            [&order]() { order.push_back("observed"); });

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  ASSERT_GE(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "observed");
}

TEST(ClockingBlockEventSim, NegedgeBlockTriggersOnNegedge) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 1);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kNegedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  auto* cb_event = f.ctx.CreateVariable("__cb_event", 1);
  cb_event->is_event = true;
  cmgr.SetBlockEventVar("cb", cb_event);

  cmgr.Attach(f.ctx, f.scheduler);

  bool triggered = false;
  cb_event->AddWatcher([&triggered]() {
    triggered = true;
    return true;
  });

  ScheduleNegedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_TRUE(triggered);
}

TEST(ClockingBlockEventSim, MultipleBlocksTriggerIndependentEvents) {
  ClockingSimFixture f;
  auto* clk1 = f.ctx.CreateVariable("clk1", 1);
  clk1->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* clk2 = f.ctx.CreateVariable("clk2", 1);
  clk2->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;

  ClockingBlock b1;
  b1.name = "cb1";
  b1.clock_signal = "clk1";
  b1.clock_edge = Edge::kPosedge;
  b1.default_input_skew = SimTime{0};
  b1.default_output_skew = SimTime{0};
  cmgr.Register(b1);

  ClockingBlock b2;
  b2.name = "cb2";
  b2.clock_signal = "clk2";
  b2.clock_edge = Edge::kPosedge;
  b2.default_input_skew = SimTime{0};
  b2.default_output_skew = SimTime{0};
  cmgr.Register(b2);

  auto* ev1 = f.ctx.CreateVariable("__cb1_event", 1);
  ev1->is_event = true;
  cmgr.SetBlockEventVar("cb1", ev1);

  auto* ev2 = f.ctx.CreateVariable("__cb2_event", 1);
  ev2->is_event = true;
  cmgr.SetBlockEventVar("cb2", ev2);

  cmgr.Attach(f.ctx, f.scheduler);

  bool ev1_fired = false;
  bool ev2_fired = false;
  ev1->AddWatcher([&ev1_fired]() {
    ev1_fired = true;
    return true;
  });
  ev2->AddWatcher([&ev2_fired]() {
    ev2_fired = true;
    return true;
  });

  SchedulePosedge(f, clk1, 10);
  f.scheduler.Run();

  EXPECT_TRUE(ev1_fired);
  EXPECT_FALSE(ev2_fired);
}

TEST(ClockingBlockEventSim, EventFiresAfterNBARegion) {
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

  std::vector<std::string> order;

  auto* nba_ev = f.scheduler.GetEventPool().Acquire();
  nba_ev->callback = [&order]() { order.push_back("nba"); };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kNBA, nba_ev);

  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler,
                            [&order]() { order.push_back("observed"); });

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  ASSERT_GE(order.size(), 2u);
  EXPECT_EQ(order[0], "nba");
  EXPECT_EQ(order[1], "observed");
}

TEST(ClockingBlockEventSim, MultipleWatchersAllFireOnEdge) {
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

  auto* cb_event = f.ctx.CreateVariable("__cb_event", 1);
  cb_event->is_event = true;
  cmgr.SetBlockEventVar("cb", cb_event);

  cmgr.Attach(f.ctx, f.scheduler);

  bool watcher_a = false;
  bool watcher_b = false;
  cb_event->AddWatcher([&watcher_a]() {
    watcher_a = true;
    return true;
  });
  cb_event->AddWatcher([&watcher_b]() {
    watcher_b = true;
    return true;
  });

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

  ClockingBlock b1;
  b1.name = "cb1";
  b1.clock_signal = "clk";
  b1.clock_edge = Edge::kPosedge;
  b1.default_input_skew = SimTime{0};
  b1.default_output_skew = SimTime{0};
  cmgr.Register(b1);

  ClockingBlock b2;
  b2.name = "cb2";
  b2.clock_signal = "clk";
  b2.clock_edge = Edge::kPosedge;
  b2.default_input_skew = SimTime{0};
  b2.default_output_skew = SimTime{0};
  cmgr.Register(b2);

  auto* ev1 = f.ctx.CreateVariable("__cb1_event", 1);
  ev1->is_event = true;
  cmgr.SetBlockEventVar("cb1", ev1);

  auto* ev2 = f.ctx.CreateVariable("__cb2_event", 1);
  ev2->is_event = true;
  cmgr.SetBlockEventVar("cb2", ev2);

  cmgr.Attach(f.ctx, f.scheduler);

  bool ev1_fired = false;
  bool ev2_fired = false;
  ev1->AddWatcher([&ev1_fired]() {
    ev1_fired = true;
    return true;
  });
  ev2->AddWatcher([&ev2_fired]() {
    ev2_fired = true;
    return true;
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_TRUE(ev1_fired);
  EXPECT_TRUE(ev2_fired);
}

}  // namespace
