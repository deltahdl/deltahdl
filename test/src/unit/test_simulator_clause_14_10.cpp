#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Register a clocking block named `name` on signal `signal` with the given
// clock `edge` and zero default input/output skews.
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

// Create an event variable named `var_name`, flag it as an event, and bind it
// to the clocking block `block_name`.
Variable* MakeBlockEvent(ClockingSimFixture& f, ClockingManager& cmgr,
                         const char* var_name, const char* block_name) {
  auto* ev = f.ctx.CreateVariable(var_name, 1);
  ev->is_event = true;
  cmgr.SetBlockEventVar(block_name, ev);
  return ev;
}

// Add a watcher to `ev` that sets *flag true when fired.
void WatchFlag(Variable* ev, bool* flag) {
  ev->AddWatcher([flag]() {
    *flag = true;
    return true;
  });
}

// Standard single-block event setup: create clk (initial `clk_init`), register
// a "cb" block on "clk" with the given edge, create+bind its "__cb_event", and
// attach. Returns clk; fills *out_event with the bound event variable.
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

// Parameters for SetupTwoBlockEvents: the two clock signals to register blocks
// on (`sig1`/`sig2`) and the two flags (`fired1`/`fired2`) set when each event
// fires.
struct TwoBlockEventSpec {
  const char* sig1;
  const char* sig2;
  bool* fired1;
  bool* fired2;
};

// Wire two posedge blocks "cb1"/"cb2" (on signals `spec.sig1`/`spec.sig2`),
// bind their "__cb1_event"/"__cb2_event" events, attach, and install watchers
// that set *spec.fired1/*spec.fired2 true when the respective event fires.
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

// Region-ordering check: schedule an event tagged `pre_label` in `pre_region`
// at t=10, register an "observed"-region edge callback on a posedge "cb" block,
// then verify the pre-region event fires before the clocking edge callback.
void RunRegionOrderingTest(ClockingSimFixture& f, Region pre_region,
                           const char* pre_label) {
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  RegisterClockBlock(cmgr, "cb", "clk", Edge::kPosedge);

  std::vector<std::string> order;

  auto* pre_ev = f.scheduler.GetEventPool().Acquire();
  pre_ev->callback = [&order, pre_label]() { order.push_back(pre_label); };
  f.scheduler.ScheduleEvent(SimTime{10}, pre_region, pre_ev);

  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler,
                            [&order]() { order.push_back("observed"); });

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  ASSERT_GE(order.size(), 2u);
  EXPECT_EQ(order[0], pre_label);
  EXPECT_EQ(order[1], "observed");
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

TEST(ClockingBlockEventSim, EventFiresInObservedRegion) {
  ClockingSimFixture f;
  RunRegionOrderingTest(f, Region::kActive, "active");
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

TEST(ClockingBlockEventSim, EventFiresAfterNBARegion) {
  ClockingSimFixture f;
  RunRegionOrderingTest(f, Region::kNBA, "nba");
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

}  // namespace
