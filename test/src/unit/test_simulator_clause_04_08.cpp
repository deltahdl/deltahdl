#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

static void ScheduleAssignAndDisplay(Scheduler& sched, int& q, int& p,
                                     int& display_out) {
  q = 0;
  auto* update_p = sched.GetEventPool().Acquire();
  update_p->kind = EventKind::kUpdate;
  update_p->callback = [&]() { p = q; };
  sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);

  auto* display = sched.GetEventPool().Acquire();
  display->kind = EventKind::kEvaluation;
  display->callback = [&]() { display_out = p; };
  sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, display);
}

TEST(SimCh48, EvalAndUpdateEventsIntermingleInActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() { order.push_back("eval"); };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  auto* update = sched.GetEventPool().Acquire();
  update->kind = EventKind::kUpdate;
  update->callback = [&]() { order.push_back("update"); };
  sched.ScheduleEvent({0}, Region::kActive, update);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);

  EXPECT_TRUE((order[0] == "eval" && order[1] == "update") ||
              (order[0] == "update" && order[1] == "eval"));
}

TEST(SimCh48, BlockingAssignmentTriggersUpdateEvent) {
  Arena arena;
  Scheduler sched(arena);
  int q = 1;
  int p = 1;

  auto* assign_q = sched.GetEventPool().Acquire();
  assign_q->kind = EventKind::kEvaluation;
  assign_q->callback = [&]() {
    q = 0;

    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);
  };
  sched.ScheduleEvent({1}, Region::kActive, assign_q);

  sched.Run();
  EXPECT_EQ(q, 0);
  EXPECT_EQ(p, 0);
}

TEST(SimCh48, UpdateEventRacesWithProcessContinuation) {
  Arena arena;
  Scheduler sched(arena);
  int p = 1;
  int q = 1;
  int display_value = -1;

  auto* process = sched.GetEventPool().Acquire();
  process->kind = EventKind::kEvaluation;
  process->callback = [&]() {
    ScheduleAssignAndDisplay(sched, q, p, display_value);
  };
  sched.ScheduleEvent({1}, Region::kActive, process);

  sched.Run();

  EXPECT_TRUE(display_value == 0 || display_value == 1);
}

TEST(SimCh48, BothRaceOutcomesAreValid) {
  Arena arena;
  Scheduler sched(arena);
  int p = 1;
  std::vector<int> observed_p;

  auto* update_p = sched.GetEventPool().Acquire();
  update_p->kind = EventKind::kUpdate;
  update_p->callback = [&]() { p = 0; };
  sched.ScheduleEvent({1}, Region::kActive, update_p);

  auto* read_p = sched.GetEventPool().Acquire();
  read_p->kind = EventKind::kEvaluation;
  read_p->callback = [&]() { observed_p.push_back(p); };
  sched.ScheduleEvent({1}, Region::kActive, read_p);

  sched.Run();
  ASSERT_EQ(observed_p.size(), 1u);

  EXPECT_TRUE(observed_p[0] == 0 || observed_p[0] == 1);
}

TEST(SimCh48, LRMExampleAssignPEqualsQ) {
  Arena arena;
  Scheduler sched(arena);
  int q = 0;
  int p = 0;
  int display_result = -1;

  auto* init_q = sched.GetEventPool().Acquire();
  init_q->kind = EventKind::kEvaluation;
  init_q->callback = [&]() {
    q = 1;

    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);
  };
  sched.ScheduleEvent({0}, Region::kActive, init_q);

  auto* assign_zero = sched.GetEventPool().Acquire();
  assign_zero->kind = EventKind::kEvaluation;
  assign_zero->callback = [&]() {
    ScheduleAssignAndDisplay(sched, q, p, display_result);
  };
  sched.ScheduleEvent({1}, Region::kActive, assign_zero);

  sched.Run();

  EXPECT_TRUE(display_result == 0 || display_result == 1);
}

TEST(SimCh48, MultipleUpdateEventsRaceWithEachOther) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int c = 0;

  auto* u1 = sched.GetEventPool().Acquire();
  u1->kind = EventKind::kUpdate;
  u1->callback = [&]() { a = 1; };
  sched.ScheduleEvent({0}, Region::kActive, u1);

  auto* u2 = sched.GetEventPool().Acquire();
  u2->kind = EventKind::kUpdate;
  u2->callback = [&]() { b = 2; };
  sched.ScheduleEvent({0}, Region::kActive, u2);

  auto* u3 = sched.GetEventPool().Acquire();
  u3->kind = EventKind::kUpdate;
  u3->callback = [&]() { c = 3; };
  sched.ScheduleEvent({0}, Region::kActive, u3);

  sched.Run();

  EXPECT_EQ(a, 1);
  EXPECT_EQ(b, 2);
  EXPECT_EQ(c, 3);
}

TEST(SimCh48, RaceConditionAcrossMultipleNets) {
  Arena arena;
  Scheduler sched(arena);
  int x = 0;
  int y = 0;
  int net_x = 0;
  int net_y = 0;
  int observed_net_x = -1;
  int observed_net_y = -1;

  auto* process = sched.GetEventPool().Acquire();
  process->kind = EventKind::kEvaluation;
  process->callback = [&]() {
    x = 10;
    y = 20;

    auto* ux = sched.GetEventPool().Acquire();
    ux->kind = EventKind::kUpdate;
    ux->callback = [&]() { net_x = x; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, ux);

    auto* uy = sched.GetEventPool().Acquire();
    uy->kind = EventKind::kUpdate;
    uy->callback = [&]() { net_y = y; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, uy);

    auto* observe = sched.GetEventPool().Acquire();
    observe->kind = EventKind::kEvaluation;
    observe->callback = [&]() {
      observed_net_x = net_x;
      observed_net_y = net_y;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, observe);
  };
  sched.ScheduleEvent({0}, Region::kActive, process);

  sched.Run();

  EXPECT_EQ(net_x, 10);
  EXPECT_EQ(net_y, 20);

  EXPECT_TRUE(observed_net_x == 0 || observed_net_x == 10);
  EXPECT_TRUE(observed_net_y == 0 || observed_net_y == 20);
}

TEST(SimCh48, EvalAndUpdateEventKindsDistinct) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<EventKind> kinds;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() { kinds.push_back(EventKind::kEvaluation); };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  auto* update = sched.GetEventPool().Acquire();
  update->kind = EventKind::kUpdate;
  update->callback = [&]() { kinds.push_back(EventKind::kUpdate); };
  sched.ScheduleEvent({0}, Region::kActive, update);

  sched.Run();
  ASSERT_EQ(kinds.size(), 2u);

  EXPECT_NE(EventKind::kEvaluation, EventKind::kUpdate);
  EXPECT_EQ(kinds[0], EventKind::kEvaluation);
  EXPECT_EQ(kinds[1], EventKind::kUpdate);
}

TEST(SimCh48, NoRaceBetweenDifferentRegions) {
  Arena arena;
  Scheduler sched(arena);
  int value = 0;
  int observed = -1;

  auto* active = sched.GetEventPool().Acquire();
  active->kind = EventKind::kUpdate;
  active->callback = [&]() { value = 42; };
  sched.ScheduleEvent({0}, Region::kActive, active);

  auto* nba = sched.GetEventPool().Acquire();
  nba->kind = EventKind::kEvaluation;
  nba->callback = [&]() { observed = value; };
  sched.ScheduleEvent({0}, Region::kNBA, nba);

  sched.Run();

  EXPECT_EQ(observed, 42);
}

TEST(SimCh48, NBAEliminatesActiveRegionRace) {
  Arena arena;
  Scheduler sched(arena);
  int q = 1;
  int p = 1;
  int display_value = -1;

  auto* process = sched.GetEventPool().Acquire();
  process->kind = EventKind::kEvaluation;
  process->callback = [&]() {

    auto* nba_q = sched.GetEventPool().Acquire();
    nba_q->kind = EventKind::kUpdate;
    nba_q->callback = [&]() {
      q = 0;

      auto* update_p = sched.GetEventPool().Acquire();
      update_p->kind = EventKind::kUpdate;
      update_p->callback = [&]() { p = q; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba_q);

    display_value = p;
  };
  sched.ScheduleEvent({0}, Region::kActive, process);

  sched.Run();

  EXPECT_EQ(display_value, 1);

  EXPECT_EQ(p, 0);
}
