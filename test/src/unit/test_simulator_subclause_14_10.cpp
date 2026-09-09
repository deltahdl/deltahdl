#include <string>

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

// Add a watcher to `ev` that appends `label` to *order when fired, so the
// firing can be ordered relative to events placed in other scheduler regions.
void WatchOrder(Variable* ev, std::vector<std::string>* order,
                const char* label) {
  ev->AddWatcher([order, label]() {
    order->push_back(label);
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

// §14.10: a clocking block triggers its named event upon its specified clocking
// event. A block declared with the any-edge form (Edge::kEdge) takes either
// transition as its clocking event, so both a rising and a falling edge trigger
// the block event, unlike the posedge/negedge blocks that react to a single
// direction.
TEST(ClockingBlockEventSim, AnyEdgeBlockTriggersOnBothEdges) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  Variable* cb_event = nullptr;
  auto* clk = SetupSingleBlockEvent(f, cmgr, Edge::kEdge, 0, &cb_event);

  // A watcher answers whether it is finished: NotifyWatchers re-registers the
  // ones that return false and drops the ones that return true. Counting two
  // firings therefore needs a watcher that stays registered through the first,
  // which is what separates this from the single-shot flags the tests above
  // use. Returning true here would unregister it at the rising edge and cap the
  // count at one whatever the block did on the falling edge.
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

// §14.10: the event *associated with the clocking block name* (the clocking
// block event) shall be triggered in the Observed region. This test watches the
// bound event variable itself (the object §14.10 names) and confirms its notify
// lands in Observed by ordering it against competing Active- and NBA-region
// events in the same time step. If the block-event notify were scheduled into
// the active region set instead of Observed it would fire before the NBA event,
// so the strict "block_event last" ordering discriminates the Observed
// placement.
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

// Drives `clk` to `value` at `time` the way an ordinary assignment does: the
// value changes and its watchers are notified, and nothing writes
// Variable::prev_value.
//
// SchedulePosedge in helpers_clocking.h writes that field before every toggle,
// which stands in for an event control armed on the same clock. §14.10 makes
// the clocking event the transition of the block's own clocking expression, so
// it has to be detected whether or not anything else waits on that clock; these
// cases drive the clock without the write so the block is left to detect the
// transition on its own.
void ScheduleClockValue(ClockingSimFixture& f, Variable* clk, uint64_t value,
                        uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, value, &f]() {
    clk->value = MakeLogic4VecVal(f.arena, 1, value);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

// §14.10: the block's event fires on each posedge of its clocking expression
// and on no other notification. The clock is driven low, high, low, high, and
// nothing else waits on it. Reading the previous value from a field nobody
// wrote leaves it at 0, which makes every notification look like a posedge, so
// the count is what tells the two apart.
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

// §14.10, the other edge: a negedge block fires when its clock falls. A
// previous value read as 0 makes a negedge impossible, so a posedge case alone
// cannot tell a working record from a missing one -- the two failures are
// opposite.
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

// §14.10: "Upon processing its specified clocking event, a clocking block shall
// trigger the event associated with the clocking block name. This event shall
// be triggered in the Observed region and is referred to as a clocking block
// event." The cases above drive ClockingManager::NotifyBlockEvent through a
// manager and an event variable the test builds itself, which says nothing
// about whether a design's `always @(cb)` attaches to anything. This one starts
// from source, on §14.10's own example shape.
//
// The clock rises twice, at t=5 and t=15, so a process attached to the block's
// event runs twice; one attached to nothing runs not at all and leaves hits at
// its declared 0.
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

// §14.10's event is the block's own, so a clock edge that is not the one the
// block names triggers nothing. The declaration here is on `negedge clk` while
// the run drives two rises and one fall, so a process that followed the raw
// variable rather than the declared edge would reach a different count.
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

// The root-cause guard under both cases above and under
// SyncDriveSim.SynchronousDriveFromSourceDrivesTheSignal: a design carrying a
// clocking block leaves the run with a ClockingManager holding it. Without
// this, a fix that wires one construct and not the other leaves the unwired one
// failing for a reason the two counts report identically.
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

// §14.3 declares a clocking block within its module, so a block written in a
// module that is instantiated belongs to the instance rather than to the
// module: the clock it names, the signals it samples and the event it triggers
// are all that instance's. The cases below declare the block one level down and
// read the result back under the instance's own prefix.

// §14.10's clocking block event, triggered by a block a child instance
// declares. The clock rises twice, so the child's `always @(cb)` runs twice; a
// block registered nowhere leaves that process attached to nothing and `hits`
// at its declared 0.
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

}  // namespace
