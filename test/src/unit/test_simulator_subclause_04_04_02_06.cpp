#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/checker_scheduling_semantics.h"
#include "simulator/scheduler.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

using namespace delta;

TEST(ReactiveRegionSim, ReactiveSelfLoopSchedulesMoreReactiveEvents) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() {
    order.push_back(1);
    auto* next = sched.GetEventPool().Acquire();
    next->callback = [&order]() { order.push_back(2); };
    sched.ScheduleEvent({0}, Region::kReactive, next);
  };
  sched.ScheduleEvent({0}, Region::kReactive, ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

TEST(ReactiveRegionSim, ReactiveRegionEmptyDoesNotBlockOtherRegions) {
  Arena arena;
  Scheduler sched(arena);
  bool observed_fired = false;
  bool postponed_fired = false;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() { observed_fired = true; };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  auto* post = sched.GetEventPool().Acquire();
  post->callback = [&]() { postponed_fired = true; };
  sched.ScheduleEvent({0}, Region::kPostponed, post);

  sched.Run();
  EXPECT_TRUE(observed_fired);
  EXPECT_TRUE(postponed_fired);
}

TEST(ReactiveRegionSim, ReactiveExecutesBeforeReInactive) {
  VerifyTwoRegionOrder({Region::kReactive, "reactive"},
                       {Region::kReInactive, "reinactive"});
}

TEST(ReactiveRegionSim, ReactiveExecutesAfterObservedAndPostObserved) {
  VerifyThreeRegionOrder({Region::kObserved, "observed"},
                         {Region::kPostObserved, "post_observed"},
                         {Region::kReactive, "reactive"});
}

TEST(ReactiveRegionSim, ReactiveEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kReactive);
}

TEST(ReactiveRegionSim, ReactiveParticipatesInReNBAIteration) {
  VerifyIterationChain(Region::kReactive, "reactive", Region::kReNBA, "renba");
}

TEST(ReactiveRegionSim, ReactiveSchedulesActiveRestart) {
  VerifyRegionRestart({Region::kActive, "active1"},
                      {Region::kReactive, "reactive"},
                      {Region::kActive, "active2"});
}

TEST(ReactiveRegionSim, CurrentRegionIsReactiveDuringReactiveEventEvaluation) {
  Arena arena;
  Scheduler sched(arena);
  Region observed = Region::kCOUNT;

  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, Region::kReactive, ev);

  sched.Run();
  EXPECT_EQ(observed, Region::kReactive);
}

TEST(ReactiveRegionSim, ReactiveEventsAllProcessedAndAnyOrderIsAttested) {
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kReactive));

  Arena arena;
  Scheduler sched(arena);
  std::vector<int> observed;

  constexpr int kN = 5;
  for (int i = 0; i < kN; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&observed, i]() { observed.push_back(i); };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  sched.Run();
  ASSERT_EQ(observed.size(), static_cast<size_t>(kN));
  std::vector<bool> seen(kN, false);
  for (int id : observed) {
    ASSERT_GE(id, 0);
    ASSERT_LT(id, kN);
    EXPECT_FALSE(seen[id]) << "Reactive event id " << id << " seen twice";
    seen[id] = true;
  }
  for (int i = 0; i < kN; ++i) {
    EXPECT_TRUE(seen[i]) << "missing Reactive event id " << i;
  }
}

TEST(ReactiveRegionSim, ReactiveIsReactiveSetDualOfActive) {
  // §4.4.2.6/§4.4.2.7/§4.4.2.8: the reactive region set mirrors the active set
  // — Reactive is the dual of Active, Re-Inactive of Inactive, and Re-NBA of
  // NBA. A region that is not itself an active-set member (e.g. Reactive) has
  // no dual.
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kActive), Region::kReactive);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kInactive),
            Region::kReInactive);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kNBA), Region::kReNBA);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kReactive), Region::kCOUNT);

  EXPECT_TRUE(IsActiveRegionSet(Region::kActive));
  EXPECT_TRUE(IsReactiveRegionSet(Region::kReactive));
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kActive));
  EXPECT_TRUE(Scheduler::IsAnyOrderRegion(Region::kReactive));
}

// §4.4.2.6 D2, driven end-to-end from real source: a blocking assignment inside
// a program block is scheduled in the Reactive region, which the stratified
// scheduler runs strictly after the Active region of the same time slot (the
// Reactive region being the reactive-set dual of Active). Rather than stub the
// home region with a helper, this builds a genuine program block plus a design
// initial and observes the runtime consequence of the region placement: the
// program's blocking read sees the value the design's Active-region initial has
// already committed, and the program's blocking write to a shared signal wins
// over the design's Active write. Both outcomes hold only if production homes
// the program's blocking-assignment code in the Reactive region.
TEST(ReactiveRegionSim, ProgramBlockBlockingAssignRunsInReactiveRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] seen;\n"
      "  logic [7:0] shared;\n"
      "  initial begin\n"
      "    a = 8'd42;\n"
      "    shared = 8'd1;\n"
      "  end\n"
      "  program p;\n"
      "    initial begin\n"
      "      seen = a;\n"
      "      shared = 8'd99;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_FALSE(f.has_errors);

  auto* seen = f.ctx.FindVariable("seen");
  auto* shared = f.ctx.FindVariable("shared");
  ASSERT_NE(seen, nullptr);
  ASSERT_NE(shared, nullptr);

  // Reactive runs after Active: the program's read observes the value the
  // design's Active-region initial committed.
  EXPECT_EQ(seen->value.ToUint64(), 42u);
  // Reactive runs after Active: the program's blocking write is applied last.
  EXPECT_EQ(shared->value.ToUint64(), 99u);
}

// §4.4.2.6 D2, checker input form: a blocking assignment appearing in a checker
// body is scheduled in the Reactive region. Unlike a program block, a checker
// body has no execution path in this simulator — the rule is realized entirely
// as the static region placement the lowering consults, so it is observed at
// that single stage via the production mapping rather than end-to-end. A
// nonblocking update to a checker variable, by contrast, is homed in Re-NBA,
// which pins down that the Reactive placement is specific to blocking code.
TEST(ReactiveRegionSim, CheckerBlockingAssignmentHomeIsReactive) {
  EXPECT_EQ(HomeRegionForCheckerStatement(CheckerStatementKind::kBlocking),
            Region::kReactive);
  EXPECT_NE(HomeRegionForCheckerStatement(
                CheckerStatementKind::kCheckerVariableNonblocking),
            Region::kReactive);
}

// §4.4.2.6 D2, concurrent-assertion input form: the code in an action block of
// a concurrent assertion is scheduled in the Reactive region. The action arm
// runs from the assertion engine's fail/pass callback whose home region the
// engine fixes to Reactive, so the rule is observed at that stage via the
// production region selector the engine uses to schedule the action.
TEST(ReactiveRegionSim, ConcurrentAssertionActionBlockHomeIsReactive) {
  EXPECT_EQ(ConcurrentAssertActionRegion(), Region::kReactive);
}
