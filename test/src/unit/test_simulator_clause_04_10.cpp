#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

static void ScheduleActiveWithNba(Scheduler& sched,
                                  std::vector<std::string>& order) {
  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() {
    order.push_back("active");
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);
}

static void ScheduleActiveEvent(Scheduler& sched,
                                std::vector<std::string>& order) {
  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() { order.push_back("active"); };
  sched.ScheduleEvent({0}, Region::kActive, active);
}

TEST(PliCallbackControlSim, ImmediateExecutionCallback) {
  Arena arena;
  Scheduler sched(arena);
  bool callback_fired = false;
  bool activity_occurred = false;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    activity_occurred = true;

    callback_fired = true;

    EXPECT_TRUE(activity_occurred);
    EXPECT_TRUE(callback_fired);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_TRUE(activity_occurred);
  EXPECT_TRUE(callback_fired);
}

TEST(PliCallbackControlSim, OneShotEvaluationEvent) {
  Arena arena;
  Scheduler sched(arena);
  int fire_count = 0;

  auto* oneshot = sched.GetEventPool().Acquire();
  oneshot->kind = EventKind::kEvaluation;
  oneshot->callback = [&]() { fire_count++; };
  sched.ScheduleEvent({0}, Region::kPreActive, oneshot);

  sched.Run();

  EXPECT_EQ(fire_count, 1);
}

TEST(PliCallbackControlSim, CbAfterDelayInPreActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_active_cb"); };
  sched.ScheduleEvent({5}, Region::kPreActive, cb);

  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() { order.push_back("active_event"); };
  sched.ScheduleEvent({5}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active_cb");
  EXPECT_EQ(order[1], "active_event");
}

TEST(PliCallbackControlSim, CbNextSimTimeInPreActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_active_nextsim"); };
  sched.ScheduleEvent({10}, Region::kPreActive, cb);

  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() { order.push_back("active_event"); };
  sched.ScheduleEvent({10}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active_nextsim");
  EXPECT_EQ(order[1], "active_event");
}

TEST(PliCallbackControlSim, CbAtStartOfSimTimeInPreActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_active_start"); };
  sched.ScheduleEvent({0}, Region::kPreActive, cb);

  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() { order.push_back("active_event"); };
  sched.ScheduleEvent({0}, Region::kActive, active);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active_start");
  EXPECT_EQ(order[1], "active_event");
}

TEST(PliCallbackControlSim, CbNbaSynchInPreNba) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleActiveWithNba(sched, order);

  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_nba_cb"); };
  sched.ScheduleEvent({0}, Region::kPreNBA, cb);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_nba_cb");
  EXPECT_EQ(order[2], "nba");
}

TEST(PliCallbackControlSim, CbReadWriteSynchInPreNbaOrPostNba) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleActiveWithNba(sched, order);

  auto* pre = sched.GetEventPool().Acquire();
  pre->kind = EventKind::kEvaluation;
  pre->callback = [&]() { order.push_back("pre_nba_rw"); };
  sched.ScheduleEvent({0}, Region::kPreNBA, pre);

  auto* post = sched.GetEventPool().Acquire();
  post->kind = EventKind::kEvaluation;
  post->callback = [&]() { order.push_back("post_nba_rw"); };
  sched.ScheduleEvent({0}, Region::kPostNBA, post);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_nba_rw");
  EXPECT_EQ(order[2], "nba");
  EXPECT_EQ(order[3], "post_nba_rw");
}

TEST(PliCallbackControlSim, CbAtEndOfSimTimeInPrePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleActiveEvent(sched, order);

  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("pre_postponed_cb"); };
  sched.ScheduleEvent({0}, Region::kPrePostponed, cb);

  auto* postponed = sched.GetEventPool().Acquire();
  postponed->kind = EventKind::kEvaluation;
  postponed->callback = [&]() { order.push_back("postponed"); };
  sched.ScheduleEvent({0}, Region::kPostponed, postponed);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "pre_postponed_cb");
  EXPECT_EQ(order[2], "postponed");
}

TEST(PliCallbackControlSim, CbReadOnlySynchInPostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleActiveEvent(sched, order);

  auto* cb = sched.GetEventPool().Acquire();
  cb->kind = EventKind::kEvaluation;
  cb->callback = [&]() { order.push_back("postponed_cb"); };
  sched.ScheduleEvent({0}, Region::kPostponed, cb);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "active");
  EXPECT_EQ(order[1], "postponed_cb");
}

static void ScheduleOrderEvent(Scheduler& sched, SimTime time, Region region,
                               std::vector<std::string>& order,
                               const std::string& label) {
  auto* ev = sched.GetEventPool().Acquire();
  ev->kind = EventKind::kEvaluation;
  ev->callback = [&order, label]() { order.push_back(label); };
  sched.ScheduleEvent(time, region, ev);
}

TEST(PliCallbackControlSim, FullPliCallbackRegionOrdering) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleOrderEvent(sched, SimTime{0}, Region::kPreActive, order,
                     "pre_active");

  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kEvaluation;
  active->callback = [&]() {
    order.push_back("active");
    auto* nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&order]() { order.push_back("nba"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, active);

  ScheduleOrderEvent(sched, SimTime{0}, Region::kPreNBA, order, "pre_nba");

  ScheduleOrderEvent(sched, SimTime{0}, Region::kPostNBA, order, "post_nba");

  ScheduleOrderEvent(sched, SimTime{0}, Region::kPrePostponed, order,
                     "pre_postponed");

  ScheduleOrderEvent(sched, SimTime{0}, Region::kPostponed, order, "postponed");

  sched.Run();
  const std::vector<std::string> kExpected = {
      "pre_active", "active",        "pre_nba",  "nba",
      "post_nba",   "pre_postponed", "postponed"};
  EXPECT_EQ(order, kExpected);
}
