#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/assertion.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

using namespace delta;

TEST(ObservedRegionSim, ObservedRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kObserved, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(ObservedRegionSim, ObservedExecutesAfterActiveRegionSet) {
  VerifyFourRegionOrder({Region::kActive, "active"},
                        {Region::kInactive, "inactive"}, {Region::kNBA, "nba"},
                        {Region::kObserved, "observed"});
}

TEST(ObservedRegionSim, ObservedToActiveRestart) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() {
    order.push_back("observed");

    auto* act = sched.GetEventPool().Acquire();
    act->callback = [&order]() { order.push_back("active_restart"); };
    sched.ScheduleEvent({0}, Region::kActive, act);
  };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "active_restart");
}

TEST(ObservedRegionSim, ObservedIsAfterPostNBABeforePostObserved) {
  auto observed_ord = static_cast<int>(Region::kObserved);
  auto post_nba_ord = static_cast<int>(Region::kPostNBA);
  auto post_observed_ord = static_cast<int>(Region::kPostObserved);
  EXPECT_GT(observed_ord, post_nba_ord);
  EXPECT_LT(observed_ord, post_observed_ord);
}

TEST(ObservedRegionSim, PreObservedExecutesBeforeObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() { order.push_back("observed"); };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  auto* pre_obs = sched.GetEventPool().Acquire();
  pre_obs->callback = [&]() { order.push_back("pre_observed"); };
  sched.ScheduleEvent({0}, Region::kPreObserved, pre_obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_observed");
  EXPECT_EQ(order[1], "observed");
}

TEST(ObservedRegionSim, ObservedExecutesBeforePostObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* post_obs = sched.GetEventPool().Acquire();
  post_obs->callback = [&]() { order.push_back("post_observed"); };
  sched.ScheduleEvent({0}, Region::kPostObserved, post_obs);

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() { order.push_back("observed"); };
  sched.ScheduleEvent({0}, Region::kObserved, obs);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "post_observed");
}

TEST(ObservedRegionSim, PliCallbackScheduledIntoObservedIsRejected) {
  Arena arena;
  Scheduler sched(arena);
  bool ran = false;

  auto* pli = sched.GetEventPool().Acquire();
  pli->kind = EventKind::kPli;
  pli->callback = [&]() { ran = true; };
  sched.ScheduleEvent({0}, Region::kObserved, pli);

  sched.Run();
  EXPECT_EQ(sched.IllegalObservedPliCount(), 1u);
  EXPECT_FALSE(ran);
}

TEST(ObservedRegionSim, PliCallbackInPreObservedIsNotRejected) {
  Arena arena;
  Scheduler sched(arena);
  bool ran = false;

  auto* pli = sched.GetEventPool().Acquire();
  pli->kind = EventKind::kPli;
  pli->callback = [&]() { ran = true; };
  sched.ScheduleEvent({0}, Region::kPreObserved, pli);

  sched.Run();
  EXPECT_EQ(sched.IllegalObservedPliCount(), 0u);
  EXPECT_TRUE(ran);
}

TEST(ObservedRegionSim, EvaluationEventInObservedIsAllowed) {
  Arena arena;
  Scheduler sched(arena);
  bool ran = false;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() { ran = true; };
  sched.ScheduleEvent({0}, Region::kObserved, eval);

  sched.Run();
  EXPECT_EQ(sched.IllegalObservedPliCount(), 0u);
  EXPECT_TRUE(ran);
}

TEST(ObservedRegionSim, EveryAttemptedPliInObservedIsCounted) {
  Arena arena;
  Scheduler sched(arena);

  for (int i = 0; i < 4; ++i) {
    auto* pli = sched.GetEventPool().Acquire();
    pli->kind = EventKind::kPli;
    pli->callback = []() {};
    sched.ScheduleEvent({0}, Region::kObserved, pli);
  }

  sched.Run();
  EXPECT_EQ(sched.IllegalObservedPliCount(), 4u);
}

TEST(ObservedRegionSim, ObservedEventsAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;

  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, Region::kObserved, ev);
  }

  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// §4.4.2.5 D1: the Observed region is for evaluation of property expressions
// when they are triggered. Rather than hand-schedule a bare event into the
// Observed region, this drives the production assertion monitor: a property is
// registered against a real signal, and the signal's change is triggered
// through the same watcher mechanism edges use elsewhere in the simulator. The
// monitor's response - scheduling the property's evaluation - is entirely
// production code, and the evaluation is confirmed to run while the scheduler's
// current region is Observed. The first trigger is the monitor's per-property
// warm-up cycle (a vacuous pass that records no verdict); the post-timestep
// tick the monitor installed advances its cycle count, so the second trigger is
// the one whose property check actually runs, and it is that check which probes
// the current region.
TEST(ObservedRegionSim, TriggeredPropertyEvaluationRunsInObservedRegion) {
  SourceManager mgr;
  Arena arena;
  Scheduler sched(arena);
  DiagEngine diag(mgr);
  SimContext ctx(sched, arena, diag);

  Variable* sig = ctx.CreateVariable("sig", 8);
  ASSERT_NE(sig, nullptr);

  Region eval_region = Region::kCOUNT;
  AssertionMonitor monitor;
  SvaProperty prop;
  prop.name = "p_observed";
  prop.kind = SvaPropertyKind::kCustom;
  prop.signal_name = "sig";
  prop.custom_check = [&](uint64_t, uint64_t) {
    eval_region = sched.CurrentRegion();
    return true;
  };
  monitor.AddProperty(prop);
  monitor.Attach(ctx, sched);

  // First trigger: warm-up evaluation, no property check yet.
  sig->NotifyWatchers();
  sched.Run();
  EXPECT_EQ(eval_region, Region::kCOUNT);

  // Second trigger: the property check runs and observes its home region.
  sig->NotifyWatchers();
  sched.Run();
  EXPECT_EQ(eval_region, Region::kObserved);
  EXPECT_EQ(monitor.PassCount(), 1u);
}

// §4.4.2.5 D2: during property evaluation, pass/fail code shall be scheduled in
// the Reactive region of the current time slot. This observes the production
// SVA engine path that realizes the rule: a matured deferred report is turned
// into a scheduled action by ExecuteMaturedObservedInReactive. The call is made
// from inside an Observed-region event running at a nonzero time, mirroring the
// real flow where the pass/fail action is emitted while the property is being
// evaluated. The action records where and when it runs, confirming the engine
// homed it in the Reactive region and in the same (current) time slot.
TEST(ObservedRegionSim, PassFailActionSchedulesIntoReactiveOfCurrentSlot) {
  Arena arena;
  Scheduler sched(arena);
  SvaEngine engine;

  Region action_region = Region::kCOUNT;
  uint64_t action_time = UINT64_MAX;

  DeferredAssertion da;
  da.condition_val =
      1;  // property passed: its pass action is the one that runs
  da.instance_name = "a1";
  da.pass_action = [&]() {
    action_region = sched.CurrentRegion();
    action_time = sched.CurrentTime().ticks;
  };
  engine.QueuePendingReport("p0", da, DeferralKind::kObserved);
  engine.MatureObservedReports("p0");

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() {
    uint32_t n = engine.ExecuteMaturedObservedInReactive("p0", sched,
                                                         sched.CurrentTime());
    EXPECT_EQ(n, 1u);
  };
  sched.ScheduleEvent({5}, Region::kObserved, obs);

  sched.Run();
  EXPECT_EQ(action_region, Region::kReactive);
  EXPECT_EQ(action_time, 5u);
}

// §4.4.2.5 D2, fail input form: the rule covers both verdict arms - a failing
// property's fail code must also land in the Reactive region of the current
// slot. A failed verdict (condition value zero) drives the engine's fail
// branch, distinct from the pass branch above, yet the matured report is still
// homed in the Reactive region at the current time. Exercising the fail arm
// confirms the region/slot placement is a property of the deferral path, not of
// which verdict arm runs.
TEST(ObservedRegionSim, FailActionSchedulesIntoReactiveOfCurrentSlot) {
  Arena arena;
  Scheduler sched(arena);
  SvaEngine engine;

  Region action_region = Region::kCOUNT;
  uint64_t action_time = UINT64_MAX;

  DeferredAssertion da;
  da.condition_val =
      0;  // property failed: its fail action is the one that runs
  da.instance_name = "a1";
  da.fail_action = [&]() {
    action_region = sched.CurrentRegion();
    action_time = sched.CurrentTime().ticks;
  };
  engine.QueuePendingReport("p0", da, DeferralKind::kObserved);
  engine.MatureObservedReports("p0");

  auto* obs = sched.GetEventPool().Acquire();
  obs->callback = [&]() {
    uint32_t n = engine.ExecuteMaturedObservedInReactive("p0", sched,
                                                         sched.CurrentTime());
    EXPECT_EQ(n, 1u);
  };
  sched.ScheduleEvent({7}, Region::kObserved, obs);

  sched.Run();
  EXPECT_EQ(action_region, Region::kReactive);
  EXPECT_EQ(action_time, 7u);
}
