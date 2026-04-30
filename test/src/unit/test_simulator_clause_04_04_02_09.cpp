#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"
#include "simulator/vpi.h"

using namespace delta;

TEST(PostponedRegionSim, PostponedRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kPostponed, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

TEST(PostponedRegionSim, PostponedObservesFinalState) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 10; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* nba = sched.GetEventPool().Acquire();
  nba->callback = [&]() { value = 20; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() { value = 30; };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { value = 40; };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sampled, 40);
}

TEST(PostponedRegionSim, PostponedExecutesAfterAllOtherSimulationRegions) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kReNBA, "renba", order);
  ScheduleLabeled(sched, Region::kReInactive, "reinactive", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kInactive, "inactive", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);

  sched.Run();
  ASSERT_EQ(order.size(), 8u);
  EXPECT_EQ(order[7], "postponed");
}

TEST(PostponedRegionSim, PostponedIsLastRegionOrdinal) {
  auto postponed_ord = static_cast<int>(Region::kPostponed);
  auto pre_postponed_ord = static_cast<int>(Region::kPrePostponed);
  auto count_ord = static_cast<int>(Region::kCOUNT);
  EXPECT_GT(postponed_ord, pre_postponed_ord);
  EXPECT_EQ(postponed_ord + 1, count_ord);
}

TEST(PostponedRegionSim, PostponedDoesNotReExecuteDuringIteration) {
  Arena arena;
  Scheduler sched(arena);
  int postponed_count = 0;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { postponed_count++; };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = [&]() {
      auto* act2 = sched.GetEventPool().Acquire();
      act2->callback = []() {};
      sched.ScheduleEvent({0}, Region::kActive, act2);
    };
    sched.ScheduleEvent({0}, Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(postponed_count, 1);
}

TEST(PostponedRegionSim, PostponedAdvancesToNextTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* postponed0 = sched.GetEventPool().Acquire();
  postponed0->callback = [&]() { order.push_back("postponed_t0"); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed0);

  auto* preponed1 = sched.GetEventPool().Acquire();
  preponed1->callback = [&]() { order.push_back("preponed_t1"); };
  sched.ScheduleEvent({1}, Region::kPreponed, preponed1);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "postponed_t0");
  EXPECT_EQ(order[1], "preponed_t1");
}

TEST(PostponedRegionSim, PostponedPLIEventsExecuteInRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pli_ev = sched.GetEventPool().Acquire();
  pli_ev->callback = [&order]() { order.push_back("pli"); };
  sched.ScheduleEvent({0}, Region::kPostponed, pli_ev);

  auto* sim_ev = sched.GetEventPool().Acquire();
  sim_ev->callback = [&order]() { order.push_back("sim"); };
  sched.ScheduleEvent({0}, Region::kPostponed, sim_ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pli");
  EXPECT_EQ(order[1], "sim");
}

TEST(PostponedRegionSim, PostponedEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kPostponed);
}

// §4.4.2.9: "Within this region, it is illegal to ... schedule an event in
// any previous region within the current time slot." Postponed is the last
// region of the slot, so any current-time schedule into a non-Postponed
// region is a violation.
TEST(PostponedRegionSim, IllegalScheduleIntoPreviousRegionInCurrentTimeSlot) {
  Arena arena;
  Scheduler sched(arena);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    auto* offender = sched.GetEventPool().Acquire();
    offender->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, offender);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 1u);
}

// §4.4.2.9: scheduling into Postponed itself at the current time slot is not
// "any previous region", so it is not flagged. Likewise scheduling into a
// previous region at a *future* time slot is allowed because the rule is
// scoped to the current time slot.
TEST(PostponedRegionSim, LegalSchedulesFromPostponedAreNotFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    auto* future = sched.GetEventPool().Acquire();
    future->callback = []() {};
    sched.ScheduleEvent({1}, Region::kActive, future);
    auto* same_region = sched.GetEventPool().Acquire();
    same_region->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kPostponed, same_region);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 0u);
}

// §4.4.2.9: each illegal schedule from Postponed is counted independently.
TEST(PostponedRegionSim, MultipleIllegalSchedulesAreEachCounted) {
  Arena arena;
  Scheduler sched(arena);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    for (int i = 0; i < 3; ++i) {
      auto* ev = sched.GetEventPool().Acquire();
      ev->callback = []() {};
      sched.ScheduleEvent(sched.CurrentTime(), Region::kPrePostponed, ev);
    }
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 3u);
}

// §4.4.2.9: scheduling from non-Postponed regions (e.g. Active) into earlier
// regions of the current time slot is permitted by §4.4.2.9 — the rule is
// specific to the Postponed region.
TEST(PostponedRegionSim, ScheduleFromActiveIntoEarlierRegionIsNotFlagged) {
  Arena arena;
  Scheduler sched(arena);

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    auto* nba = sched.GetEventPool().Acquire();
    nba->callback = []() {};
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedScheduleCount(), 0u);
}

// §4.4.2.9: "it is illegal to write values to any net or variable" once the
// Postponed region is reached. The VPI write path (VpiContext::PutValue)
// is the canonical write entry point; when invoked from a Postponed callback
// the scheduler records the violation.
TEST(PostponedRegionSim, VpiPutValueFromPostponedRecordsWriteViolation) {
  Arena arena;
  Scheduler sched(arena);
  VpiContext vpi;
  vpi.SetScheduler(&sched);

  Logic4Word storage{};
  Variable var{};
  var.value.width = 32;
  var.value.nwords = 1;
  var.value.words = &storage;

  VpiObject obj{};
  obj.var = &var;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 42;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 0u);
  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 1u);
}

// §4.4.2.9 ¶3: each illegal write from Postponed must be counted independently
// — mirrors the multi-count behavior of the schedule violation counter so the
// "no new value changes" rule remains observable across repeated VPI writes.
TEST(PostponedRegionSim, MultipleIllegalWritesAreEachCounted) {
  Arena arena;
  Scheduler sched(arena);
  VpiContext vpi;
  vpi.SetScheduler(&sched);

  Logic4Word storage{};
  Variable var{};
  var.value.width = 32;
  var.value.nwords = 1;
  var.value.words = &storage;

  VpiObject obj{};
  obj.var = &var;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() {
    for (int i = 0; i < 4; ++i) {
      VpiValue value{};
      value.format = kVpiIntVal;
      value.value.integer = i;
      vpi.PutValue(&obj, &value, nullptr, 0);
    }
  };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 4u);
}

// §4.4.2.9: VPI writes from regions other than Postponed are not flagged —
// the rule is scoped to the Postponed region.
TEST(PostponedRegionSim, VpiPutValueOutsidePostponedDoesNotRecordViolation) {
  Arena arena;
  Scheduler sched(arena);
  VpiContext vpi;
  vpi.SetScheduler(&sched);

  Logic4Word storage{};
  Variable var{};
  var.value.width = 32;
  var.value.nwords = 1;
  var.value.words = &storage;

  VpiObject obj{};
  obj.var = &var;

  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() {
    VpiValue value{};
    value.format = kVpiIntVal;
    value.value.integer = 42;
    vpi.PutValue(&obj, &value, nullptr, 0);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  EXPECT_EQ(sched.IllegalPostponedWriteCount(), 0u);
  EXPECT_EQ(var.value.words[0].aval, 42u);
}

// §4.4.2.9 ¶1: "$monitor, $strobe, and other similar events are scheduled
// in the Postponed region." EvalDeferredPrint is the production-code routing
// path: it acquires an event whose callback emits the formatted output and
// schedules it into Region::kPostponed. To observe the rule, we capture
// std::cout, run a $strobe inside an initial block, and snapshot the buffer
// from a Pre-Postponed sentinel. The strobe text must be absent at the
// Pre-Postponed sample (i.e. not emitted by an earlier region) and present
// after the run completes — the only remaining region after Pre-Postponed
// where the deferred print could have fired is Postponed itself.
TEST(PostponedRegionSim, StrobeIsScheduledIntoPostponedRegion) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());

  LowerFixture f;
  std::string snapshot_at_pre_postponed;
  auto* spy = f.scheduler.GetEventPool().Acquire();
  spy->callback = [&]() { snapshot_at_pre_postponed = captured.str(); };
  f.scheduler.ScheduleEvent({0}, Region::kPrePostponed, spy);

  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $strobe(\"DELTA_STROBE_TAG\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  std::cout.rdbuf(old_buf);

  EXPECT_EQ(snapshot_at_pre_postponed.find("DELTA_STROBE_TAG"),
            std::string::npos)
      << "snapshot=" << snapshot_at_pre_postponed;
  EXPECT_NE(captured.str().find("DELTA_STROBE_TAG"), std::string::npos)
      << "captured=" << captured.str();
}

// §4.4.2.9 ¶1: $monitor takes the same EvalDeferredPrint path and must also
// land in the Postponed region. Asserting both system tasks separately keeps
// the rule observable for each name listed in the LRM text.
TEST(PostponedRegionSim, MonitorIsScheduledIntoPostponedRegion) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());

  LowerFixture f;
  std::string snapshot_at_pre_postponed;
  auto* spy = f.scheduler.GetEventPool().Acquire();
  spy->callback = [&]() { snapshot_at_pre_postponed = captured.str(); };
  f.scheduler.ScheduleEvent({0}, Region::kPrePostponed, spy);

  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial $monitor(\"DELTA_MONITOR_TAG\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  std::cout.rdbuf(old_buf);

  EXPECT_EQ(snapshot_at_pre_postponed.find("DELTA_MONITOR_TAG"),
            std::string::npos)
      << "snapshot=" << snapshot_at_pre_postponed;
  EXPECT_NE(captured.str().find("DELTA_MONITOR_TAG"), std::string::npos)
      << "captured=" << captured.str();
}

// §4.4.2.9: while executing Postponed, the scheduler reports the current
// region so net/variable write paths can apply the "no new value changes"
// restriction.
TEST(PostponedRegionSim, CurrentRegionIsPostponedDuringPostponedCallback) {
  Arena arena;
  Scheduler sched(arena);
  Region observed = Region::kCOUNT;

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->callback = [&]() { observed = sched.CurrentRegion(); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  EXPECT_EQ(observed, Region::kPostponed);
}
