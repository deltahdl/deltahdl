#pragma once

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "simulator/scheduler.h"

using namespace delta;

struct RegionLabel {
  Region region;
  std::string label;
};

// Schedule a labeled event at time 0.
inline void ScheduleLabeled(Scheduler& sched, Region region,
                            const std::string& label,
                            std::vector<std::string>& order) {
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&order, label]() { order.push_back(label); };
  sched.ScheduleEvent({0}, region, ev);
}

// Schedule a labeled event at an explicit time.
inline void ScheduleLabeled(Scheduler& sched, uint64_t time, Region region,
                            const std::string& label,
                            std::vector<std::string>& order) {
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&order, label]() { order.push_back(label); };
  sched.ScheduleEvent({time}, region, ev);
}

// Verify that two regions execute in the given order.
inline void VerifyTwoRegionOrder(const RegionLabel& first,
                                 const RegionLabel& second) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  ScheduleLabeled(sched, second.region, second.label, order);
  ScheduleLabeled(sched, first.region, first.label, order);
  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], first.label);
  EXPECT_EQ(order[1], second.label);
}

// Verify that three regions execute in the given order.
inline void VerifyThreeRegionOrder(const RegionLabel& r1, const RegionLabel& r2,
                                   const RegionLabel& r3) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  ScheduleLabeled(sched, r3.region, r3.label, order);
  ScheduleLabeled(sched, r2.region, r2.label, order);
  ScheduleLabeled(sched, r1.region, r1.label, order);
  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], r1.label);
  EXPECT_EQ(order[1], r2.label);
  EXPECT_EQ(order[2], r3.label);
}

// Verify that four regions execute in the given order.
inline void VerifyFourRegionOrder(const RegionLabel& r1, const RegionLabel& r2,
                                  const RegionLabel& r3,
                                  const RegionLabel& r4) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  ScheduleLabeled(sched, r4.region, r4.label, order);
  ScheduleLabeled(sched, r3.region, r3.label, order);
  ScheduleLabeled(sched, r2.region, r2.label, order);
  ScheduleLabeled(sched, r1.region, r1.label, order);
  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], r1.label);
  EXPECT_EQ(order[1], r2.label);
  EXPECT_EQ(order[2], r3.label);
  EXPECT_EQ(order[3], r4.label);
}

// Verify main→side→main iteration (e.g., Active→NBA→Active).
inline void VerifyIterationChain(Region main_region,
                                 const std::string& main_label,
                                 Region side_region,
                                 const std::string& side_label) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  auto* main1 = sched.GetEventPool().Acquire();
  main1->callback = [&]() {
    order.push_back(main_label + "1");
    auto* side = sched.GetEventPool().Acquire();
    side->callback = [&]() {
      order.push_back(side_label);
      auto* main2 = sched.GetEventPool().Acquire();
      main2->callback = [&order, main_label]() {
        order.push_back(main_label + "2");
      };
      sched.ScheduleEvent({0}, main_region, main2);
    };
    sched.ScheduleEvent({0}, side_region, side);
  };
  sched.ScheduleEvent({0}, main_region, main1);
  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], main_label + "1");
  EXPECT_EQ(order[1], side_label);
  EXPECT_EQ(order[2], main_label + "2");
}

// Verify region restart: initial runs, trigger schedules into target.
inline void VerifyRegionRestart(const RegionLabel& initial,
                                const RegionLabel& trigger,
                                const RegionLabel& target) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  auto* first = sched.GetEventPool().Acquire();
  first->callback = [&order, lbl = initial.label]() { order.push_back(lbl); };
  sched.ScheduleEvent({0}, initial.region, first);
  auto* trig = sched.GetEventPool().Acquire();
  trig->callback = [&, trigger_label = trigger.label,
                    target_region = target.region,
                    target_label = target.label]() {
    order.push_back(trigger_label);
    auto* restart = sched.GetEventPool().Acquire();
    restart->callback = [&order, target_label]() {
      order.push_back(target_label);
    };
    sched.ScheduleEvent({0}, target_region, restart);
  };
  sched.ScheduleEvent({0}, trigger.region, trig);
  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], initial.label);
  EXPECT_EQ(order[1], trigger.label);
  EXPECT_EQ(order[2], target.label);
}

// Verify events at times 0, 1, 2 execute in order for a given region.
inline void VerifyEventsAcrossTimeSlots(Region region) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<uint64_t> times;
  for (uint64_t t = 0; t < 3; ++t) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&times, &sched]() {
      times.push_back(sched.CurrentTime().ticks);
    };
    sched.ScheduleEvent({t}, region, ev);
  }
  sched.Run();
  ASSERT_EQ(times.size(), 3u);
  EXPECT_EQ(times[0], 0u);
  EXPECT_EQ(times[1], 1u);
  EXPECT_EQ(times[2], 2u);
}

// Verify a region can read a value set by Active.
inline void VerifyRegionCanReadActiveValue(Region reader_region) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int sampled = -1;
  auto* active = sched.GetEventPool().Acquire();
  active->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kActive, active);
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&]() { sampled = value; };
  sched.ScheduleEvent({0}, reader_region, ev);
  sched.Run();
  EXPECT_EQ(sampled, 42);
}

// Verify Active region events execute in FIFO order.
inline void VerifyActiveRegionFIFO() {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;
  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() { order.push_back(i); };
    sched.ScheduleEvent({0}, Region::kActive, ev);
  }
  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], 0);
  EXPECT_EQ(order[1], 1);
  EXPECT_EQ(order[2], 2);
}

// Verify continuous assignment corresponds to a process.
inline void VerifyCACorrespondsToProcess() {
  Arena arena;
  Scheduler sched(arena);
  int src = 0, dst = 0, process_eval_count = 0;
  auto* drive0 = sched.GetEventPool().Acquire();
  drive0->kind = EventKind::kEvaluation;
  drive0->callback = [&]() {
    src = 10;
    ++process_eval_count;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = src; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive0);
  auto* drive5 = sched.GetEventPool().Acquire();
  drive5->kind = EventKind::kEvaluation;
  drive5->callback = [&]() {
    src = 20;
    ++process_eval_count;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = src; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({5}, Region::kActive, drive5);
  sched.Run();
  EXPECT_EQ(dst, 20);
  EXPECT_EQ(process_eval_count, 2);
}

// Verify all 17 regions execute in the correct order.
inline void VerifyAllRegionOrder() {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kPrePostponed, "pre_postponed", order);
  ScheduleLabeled(sched, Region::kPostReNBA, "post_re_nba", order);
  ScheduleLabeled(sched, Region::kReNBA, "re_nba", order);
  ScheduleLabeled(sched, Region::kPreReNBA, "pre_re_nba", order);
  ScheduleLabeled(sched, Region::kReInactive, "re_inactive", order);
  ScheduleLabeled(sched, Region::kReactive, "reactive", order);
  ScheduleLabeled(sched, Region::kPostObserved, "post_observed", order);
  ScheduleLabeled(sched, Region::kObserved, "observed", order);
  ScheduleLabeled(sched, Region::kPreObserved, "pre_observed", order);
  ScheduleLabeled(sched, Region::kPostNBA, "post_nba", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);
  ScheduleLabeled(sched, Region::kPreNBA, "pre_nba", order);
  ScheduleLabeled(sched, Region::kInactive, "inactive", order);
  ScheduleLabeled(sched, Region::kActive, "active", order);
  ScheduleLabeled(sched, Region::kPreActive, "pre_active", order);
  ScheduleLabeled(sched, Region::kPreponed, "preponed", order);
  sched.Run();
  std::vector<std::string> expected = {
      "preponed",   "pre_active",    "active",      "inactive",
      "pre_nba",    "nba",           "post_nba",    "pre_observed",
      "observed",   "post_observed", "reactive",    "re_inactive",
      "pre_re_nba", "re_nba",        "post_re_nba", "pre_postponed",
      "postponed"};
  EXPECT_EQ(order, expected);
}

// Verify all regions execute in monotonically increasing ordinal order.
inline void VerifyAllRegionsExecuteInOrder() {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;
  for (int r = 0; r < static_cast<int>(Region::kCOUNT); ++r) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, r]() { order.push_back(r); };
    sched.ScheduleEvent({0}, static_cast<Region>(r), ev);
  }
  sched.Run();
  ASSERT_EQ(order.size(), kRegionCount);
  for (size_t i = 1; i < order.size(); ++i) {
    EXPECT_LT(order[i - 1], order[i]);
  }
}

// Verify CA schedules an active update event (before NBA).
inline void VerifyCASchedulesActiveUpdateEvent() {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    auto* active_update = sched.GetEventPool().Acquire();
    active_update->kind = EventKind::kUpdate;
    active_update->callback = [&]() { order.push_back("active_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, active_update);
    auto* nba_update = sched.GetEventPool().Acquire();
    nba_update->kind = EventKind::kUpdate;
    nba_update->callback = [&]() { order.push_back("nba_update"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba_update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);
  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active_update");
  EXPECT_EQ(order[1], "nba_update");
}
