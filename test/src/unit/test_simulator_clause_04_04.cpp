#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

// ===========================================================================
// §4.4 Stratified event scheduler
//
// LRM §4.4 defines the stratified event scheduler data structure:
//   - A compliant simulator shall maintain a data structure that allows
//     events to be dynamically scheduled, executed, and removed as the
//     simulator advances through time.
//   - The first division is by time: every event has one and only one
//     simulation execution time (current or future).
//   - All scheduled events at a specific time define a time slot.
//   - Simulation proceeds by executing and removing all events in the
//     current time slot before moving on to the next nonempty time slot,
//     in time order. This guarantees the simulator never goes backwards.
//   - A time slot is divided into a set of 17 ordered regions (a–q):
//     Preponed, Pre-Active, Active, Inactive, Pre-NBA, NBA, Post-NBA,
//     Pre-Observed, Observed, Post-Observed, Reactive, Re-Inactive,
//     Pre-Re-NBA, Re-NBA, Post-Re-NBA, Pre-Postponed, Postponed.
//   - The purpose of dividing a time slot into these ordered regions is
//     to provide predictable interactions between design and testbench.
// ===========================================================================

struct SimCh44Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc44(const std::string &src, SimCh44Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet44(const std::string &src, const char *var_name) {
  SimCh44Fixture f;
  auto *design = ElaborateSrc44(src, f);
  EXPECT_NE(design, nullptr);
  if (!design)
    return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var)
    return 0;
  return var->value.ToUint64();
}

// ---------------------------------------------------------------------------
// §4.4 "A compliant SystemVerilog simulator shall maintain some form of
// data structure that allows events to be dynamically scheduled, executed,
// and removed as the simulator advances through time."
//
// The Scheduler and EventPool together form this data structure.
// Verify that events can be dynamically scheduled and executed.
// ---------------------------------------------------------------------------
TEST(SimCh44, EventsDynamicallyScheduledAndExecuted) {
  Arena arena;
  Scheduler sched(arena);
  bool executed = false;

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&executed]() { executed = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  EXPECT_TRUE(sched.HasEvents());
  sched.Run();
  EXPECT_TRUE(executed);
  EXPECT_FALSE(sched.HasEvents());
}

// ---------------------------------------------------------------------------
// §4.4 Events are removed after execution — the event pool recycles them.
// ---------------------------------------------------------------------------
TEST(SimCh44, EventsRemovedAfterExecution) {
  Arena arena;
  Scheduler sched(arena);
  auto &pool = sched.GetEventPool();

  auto *ev = pool.Acquire();
  ev->callback = []() {};
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(pool.FreeCount(), 1u);
}

// ---------------------------------------------------------------------------
// §4.4 "The first division is by time. Every event has one and only one
// simulation execution time, which at any given point during simulation
// can be the current time or some future time."
//
// Events scheduled at different times are separated into distinct time slots.
// ---------------------------------------------------------------------------
TEST(SimCh44, FirstDivisionByTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> exec_times;

  sched.SetPostTimestepCallback(
      [&]() { exec_times.push_back(sched.CurrentTime().ticks); });

  for (uint64_t t : {0, 10, 20}) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = []() {};
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(exec_times.size(), 3u);
  EXPECT_EQ(exec_times[0], 0u);
  EXPECT_EQ(exec_times[1], 10u);
  EXPECT_EQ(exec_times[2], 20u);
}

// ---------------------------------------------------------------------------
// §4.4 "All scheduled events at a specific time define a time slot."
//
// Multiple events at the same time are grouped into one time slot.
// ---------------------------------------------------------------------------
TEST(SimCh44, AllEventsAtSameTimeFormOneTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  int timestep_count = 0;
  int event_count = 0;

  sched.SetPostTimestepCallback([&]() { timestep_count++; });

  for (int i = 0; i < 5; ++i) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&event_count]() { event_count++; };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }

  sched.Run();
  EXPECT_EQ(timestep_count, 1);
  EXPECT_EQ(event_count, 5);
}

// ---------------------------------------------------------------------------
// §4.4 "Simulation proceeds by executing and removing all events in the
// current simulation time slot before moving on to the next nonempty
// time slot, in time order."
//
// All events at time 5 must complete before any event at time 10 starts.
// ---------------------------------------------------------------------------
TEST(SimCh44, AllEventsInCurrentSlotBeforeNext) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::pair<uint64_t, int>> log;

  for (int i = 0; i < 3; ++i) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&log, &sched, i]() {
      log.push_back({sched.CurrentTime().ticks, i});
    };
    sched.ScheduleEvent({5}, Region::kActive, ev);
  }

  auto *ev_later = sched.GetEventPool().Acquire();
  ev_later->callback = [&log, &sched]() {
    log.push_back({sched.CurrentTime().ticks, 99});
  };
  sched.ScheduleEvent({10}, Region::kActive, ev_later);

  sched.Run();
  ASSERT_EQ(log.size(), 4u);
  EXPECT_EQ(log[0].first, 5u);
  EXPECT_EQ(log[1].first, 5u);
  EXPECT_EQ(log[2].first, 5u);
  EXPECT_EQ(log[3].first, 10u);
}

// ---------------------------------------------------------------------------
// §4.4 "This procedure guarantees that the simulator never goes backwards
// in time."
//
// Even when events are scheduled in reverse chronological order, they
// execute in forward time order.
// ---------------------------------------------------------------------------
TEST(SimCh44, SimulatorNeverGoesBackwardsInTime) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  sched.SetPostTimestepCallback(
      [&]() { times.push_back(sched.CurrentTime().ticks); });

  for (uint64_t t : {100, 50, 25, 10, 5}) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = []() {};
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 5u);
  for (size_t i = 1; i < times.size(); ++i) {
    EXPECT_GT(times[i], times[i - 1]);
  }
}

// ---------------------------------------------------------------------------
// §4.4 Empty time slots are skipped: simulation moves to "next nonempty
// time slot."
// ---------------------------------------------------------------------------
TEST(SimCh44, EmptyTimeSlotsSkipped) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  sched.SetPostTimestepCallback(
      [&]() { times.push_back(sched.CurrentTime().ticks); });

  for (uint64_t t : {0, 100, 500}) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = []() {};
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 100u);
  EXPECT_EQ(times[2], 500u);
}

// ---------------------------------------------------------------------------
// §4.4 "A time slot is divided into a set of ordered regions."
//
// There are exactly 17 regions, from Preponed (0) to Postponed (16).
// ---------------------------------------------------------------------------
TEST(SimCh44, TimeSlotHas17OrderedRegions) {
  EXPECT_EQ(kRegionCount, 17u);
  EXPECT_EQ(static_cast<int>(Region::kPreponed), 0);
  EXPECT_EQ(static_cast<int>(Region::kPostponed), 16);
}

// ---------------------------------------------------------------------------
// §4.4 Regions a–q: all 17 named regions exist and are ordered correctly.
// a) Preponed, b) Pre-Active, c) Active, d) Inactive, e) Pre-NBA,
// f) NBA, g) Post-NBA, h) Pre-Observed, i) Observed, j) Post-Observed,
// k) Reactive, l) Re-Inactive, m) Pre-Re-NBA, n) Re-NBA,
// o) Post-Re-NBA, p) Pre-Postponed, q) Postponed
// ---------------------------------------------------------------------------
TEST(SimCh44, All17RegionsNamedAndOrdered) {
  EXPECT_LT(static_cast<int>(Region::kPreponed),
            static_cast<int>(Region::kPreActive));
  EXPECT_LT(static_cast<int>(Region::kPreActive),
            static_cast<int>(Region::kActive));
  EXPECT_LT(static_cast<int>(Region::kActive),
            static_cast<int>(Region::kInactive));
  EXPECT_LT(static_cast<int>(Region::kInactive),
            static_cast<int>(Region::kPreNBA));
  EXPECT_LT(static_cast<int>(Region::kPreNBA), static_cast<int>(Region::kNBA));
  EXPECT_LT(static_cast<int>(Region::kNBA), static_cast<int>(Region::kPostNBA));
  EXPECT_LT(static_cast<int>(Region::kPostNBA),
            static_cast<int>(Region::kPreObserved));
  EXPECT_LT(static_cast<int>(Region::kPreObserved),
            static_cast<int>(Region::kObserved));
  EXPECT_LT(static_cast<int>(Region::kObserved),
            static_cast<int>(Region::kPostObserved));
  EXPECT_LT(static_cast<int>(Region::kPostObserved),
            static_cast<int>(Region::kReactive));
  EXPECT_LT(static_cast<int>(Region::kReactive),
            static_cast<int>(Region::kReInactive));
  EXPECT_LT(static_cast<int>(Region::kReInactive),
            static_cast<int>(Region::kPreReNBA));
  EXPECT_LT(static_cast<int>(Region::kPreReNBA),
            static_cast<int>(Region::kReNBA));
  EXPECT_LT(static_cast<int>(Region::kReNBA),
            static_cast<int>(Region::kPostReNBA));
  EXPECT_LT(static_cast<int>(Region::kPostReNBA),
            static_cast<int>(Region::kPrePostponed));
  EXPECT_LT(static_cast<int>(Region::kPrePostponed),
            static_cast<int>(Region::kPostponed));
}

// ---------------------------------------------------------------------------
// §4.4 All 17 regions execute within a single time slot in the correct
// monotonically increasing order.
// ---------------------------------------------------------------------------
TEST(SimCh44, AllRegionsExecuteInOrder) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  for (int r = 0; r < static_cast<int>(Region::kCOUNT); ++r) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, r]() { order.push_back(r); };
    sched.ScheduleEvent({0}, static_cast<Region>(r), ev);
  }

  sched.Run();
  ASSERT_EQ(order.size(), kRegionCount);
  for (size_t i = 1; i < order.size(); ++i) {
    EXPECT_LT(order[i - 1], order[i]);
  }
}

// ---------------------------------------------------------------------------
// §4.4 TimeSlot data structure: AnyNonemptyIn detects events in a range.
// ---------------------------------------------------------------------------
TEST(SimCh44, TimeSlotAnyNonemptyInRange) {
  Arena arena;
  EventPool pool(arena);
  TimeSlot slot;

  EXPECT_FALSE(slot.AnyNonemptyIn(Region::kActive, Region::kNBA));

  auto *ev = pool.Acquire();
  ev->callback = []() {};
  slot.regions[static_cast<size_t>(Region::kInactive)].Push(ev);

  EXPECT_TRUE(slot.AnyNonemptyIn(Region::kActive, Region::kNBA));
  EXPECT_FALSE(slot.AnyNonemptyIn(Region::kReactive, Region::kReNBA));
}

// ---------------------------------------------------------------------------
// §4.4 EventQueue: intrusive linked list maintains FIFO order.
// This is the data structure subdivision within a region.
// ---------------------------------------------------------------------------
TEST(SimCh44, EventQueueFIFOOrder) {
  Arena arena;
  EventPool pool(arena);
  EventQueue queue;

  auto *ev1 = pool.Acquire();
  auto *ev2 = pool.Acquire();
  auto *ev3 = pool.Acquire();

  queue.Push(ev1);
  queue.Push(ev2);
  queue.Push(ev3);

  EXPECT_FALSE(queue.empty());
  EXPECT_EQ(queue.Pop(), ev1);
  EXPECT_EQ(queue.Pop(), ev2);
  EXPECT_EQ(queue.Pop(), ev3);
  EXPECT_TRUE(queue.empty());
}

// ---------------------------------------------------------------------------
// §4.4 EventQueue::Clear removes all events from the queue.
// ---------------------------------------------------------------------------
TEST(SimCh44, EventQueueClear) {
  Arena arena;
  EventPool pool(arena);
  EventQueue queue;

  auto *ev = pool.Acquire();
  queue.Push(ev);
  EXPECT_FALSE(queue.empty());

  queue.Clear();
  EXPECT_TRUE(queue.empty());
}

// ---------------------------------------------------------------------------
// §4.4 "The purpose of dividing a time slot into these ordered regions is
// to provide predictable interactions between the design and testbench
// code."
//
// Verify that blocking (Active) and nonblocking (NBA) assignments produce
// predictable results because of region ordering.
// ---------------------------------------------------------------------------
TEST(SimCh44, RegionsPredictableDesignTestbenchInteraction) {
  SimCh44Fixture f;
  auto *design = ElaborateSrc44("module t;\n"
                                "  logic [7:0] a, b;\n"
                                "  initial begin\n"
                                "    a = 8'd10;\n"
                                "    b <= 8'd20;\n"
                                "  end\n"
                                "endmodule\n",
                                f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 20u);
}

// ---------------------------------------------------------------------------
// §4.4 Region ordering provides predictable interaction: always_comb
// (Active) sees the NBA update from a nonblocking assignment, allowing
// testbench and design code to interact predictably.
// ---------------------------------------------------------------------------
TEST(SimCh44, PredictableNBAToAlwaysCombInteraction) {
  SimCh44Fixture f;
  auto *design = ElaborateSrc44("module t;\n"
                                "  logic [7:0] x, y;\n"
                                "  initial x <= 8'd50;\n"
                                "  always_comb y = x + 8'd1;\n"
                                "endmodule\n",
                                f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 50u);
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 51u);
}

// ---------------------------------------------------------------------------
// §4.4 Time slot completeness: an event that dynamically schedules another
// event in the same time slot (but later region) still executes within
// the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh44, DynamicSchedulingWithinSameTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  int timestep_count = 0;
  bool inner_ran = false;

  sched.SetPostTimestepCallback([&]() { timestep_count++; });

  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    auto *inner = sched.GetEventPool().Acquire();
    inner->callback = [&inner_ran]() { inner_ran = true; };
    sched.ScheduleEvent({0}, Region::kNBA, inner);
  };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_TRUE(inner_ran);
  EXPECT_EQ(timestep_count, 1);
}

// ---------------------------------------------------------------------------
// §4.4 Time slot completeness via simulation: an initial block that uses
// both blocking and nonblocking assignments has both complete within
// the same time slot.
// ---------------------------------------------------------------------------
TEST(SimCh44, BlockingAndNBACompleteInSameTimeSlot) {
  SimCh44Fixture f;
  auto *design = ElaborateSrc44("module t;\n"
                                "  logic [7:0] a, b, c;\n"
                                "  initial begin\n"
                                "    a = 8'd1;\n"
                                "    b <= 8'd2;\n"
                                "    c = 8'd3;\n"
                                "  end\n"
                                "endmodule\n",
                                f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 3u);
}

// ---------------------------------------------------------------------------
// §4.4 Multiple time slots each contain their own complete set of events.
// Events at time 5, 10, and 15 each form separate time slots.
// ---------------------------------------------------------------------------
TEST(SimCh44, MultipleTimeSlotsFormDistinctSlots) {
  auto result = RunAndGet44("module t;\n"
                            "  logic [7:0] x;\n"
                            "  initial begin\n"
                            "    x = 8'd0;\n"
                            "    #5 x = x + 8'd1;\n"
                            "    #5 x = x + 8'd1;\n"
                            "    #5 x = x + 8'd1;\n"
                            "  end\n"
                            "endmodule\n",
                            "x");
  EXPECT_EQ(result, 3u);
}

// ---------------------------------------------------------------------------
// §4.4 "The data structure is normally implemented as a time-ordered set
// of linked lists, which are divided and subdivided in a well-defined
// manner."
//
// Verify that the event_calendar_ (std::map<SimTime, TimeSlot>) provides
// time-ordered iteration. ScheduleEvent places events correctly.
// ---------------------------------------------------------------------------
TEST(SimCh44, EventCalendarTimeOrdered) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  sched.SetPostTimestepCallback(
      [&]() { times.push_back(sched.CurrentTime().ticks); });

  for (uint64_t t : {30, 10, 50, 20, 40}) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = []() {};
    sched.ScheduleEvent({t}, Region::kActive, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 5u);
  EXPECT_EQ(times[0], 10u);
  EXPECT_EQ(times[1], 20u);
  EXPECT_EQ(times[2], 30u);
  EXPECT_EQ(times[3], 40u);
  EXPECT_EQ(times[4], 50u);
}

// ---------------------------------------------------------------------------
// §4.4 Simulation with no events: scheduler has no work, time stays at 0.
// ---------------------------------------------------------------------------
TEST(SimCh44, NoEventsNoAdvance) {
  Arena arena;
  Scheduler sched(arena);
  EXPECT_FALSE(sched.HasEvents());
  sched.Run();
  EXPECT_EQ(sched.CurrentTime().ticks, 0u);
  EXPECT_FALSE(sched.HasEvents());
}

// ---------------------------------------------------------------------------
// §4.4 Region ordering across time: regions are ordered within each time
// slot independently. Active at time 10 runs before NBA at time 10,
// and both run after all events at time 5.
// ---------------------------------------------------------------------------
TEST(SimCh44, RegionOrderingPerTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::pair<uint64_t, std::string>> log;

  auto schedule = [&](uint64_t t, Region r, const std::string &label) {
    auto *ev = sched.GetEventPool().Acquire();
    ev->callback = [&log, &sched, label]() {
      log.push_back({sched.CurrentTime().ticks, label});
    };
    sched.ScheduleEvent({t}, r, ev);
  };

  schedule(10, Region::kNBA, "t10_nba");
  schedule(10, Region::kActive, "t10_active");
  schedule(5, Region::kNBA, "t5_nba");
  schedule(5, Region::kActive, "t5_active");

  sched.Run();
  ASSERT_EQ(log.size(), 4u);
  EXPECT_EQ(log[0].second, "t5_active");
  EXPECT_EQ(log[1].second, "t5_nba");
  EXPECT_EQ(log[2].second, "t10_active");
  EXPECT_EQ(log[3].second, "t10_nba");
}
