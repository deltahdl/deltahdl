#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

TEST(ReInactiveRegionSim, ReInactiveExecutesAfterReactive) {
  VerifyTwoRegionOrder({Region::kReactive, "reactive"},
                       {Region::kReInactive, "reinactive"});
}

TEST(ReInactiveRegionSim, AllReactiveEventsCompleteBeforeReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("reactive" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kReactive, ev);
  }

  auto* reinactive = sched.GetEventPool().Acquire();
  reinactive->callback = [&]() { order.push_back("reinactive"); };
  sched.ScheduleEvent({0}, Region::kReInactive, reinactive);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  EXPECT_EQ(order[3], "reinactive");
}

// §4.4.2.7 ¶1: "after **all** the Reactive events are processed" — including
// Reactive events scheduled into the same time slot from inside another
// Reactive callback. Distinct from AllReactiveEventsCompleteBeforeReInactive,
// which pre-queues every Reactive before Run() and so never exercises the
// reentrant-push path through DrainQueue's `while (!queue.empty())` loop. If
// the loop snapshotted queue length at entry (instead of testing emptiness on
// each pop), the mid-drain reactive2 would defer past Re-Inactive and the
// observed order would put "reinactive" before "reactive2".
TEST(ReInactiveRegionSim, ReactivesScheduledDuringDrainRunBeforeReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* react1 = sched.GetEventPool().Acquire();
  react1->callback = [&]() {
    order.push_back("reactive1");
    auto* react2 = sched.GetEventPool().Acquire();
    react2->callback = [&]() { order.push_back("reactive2"); };
    sched.ScheduleEvent({0}, Region::kReactive, react2);
  };
  sched.ScheduleEvent({0}, Region::kReactive, react1);

  auto* reinactive = sched.GetEventPool().Acquire();
  reinactive->callback = [&]() { order.push_back("reinactive"); };
  sched.ScheduleEvent({0}, Region::kReInactive, reinactive);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reactive1");
  EXPECT_EQ(order[1], "reactive2");
  EXPECT_EQ(order[2], "reinactive");
}

TEST(ReInactiveRegionSim, ZeroDelaySchedulesIntoReInactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reactive = sched.GetEventPool().Acquire();
  reactive->callback = [&]() {
    order.push_back("reactive");

    auto* delayed = sched.GetEventPool().Acquire();
    delayed->callback = [&order]() { order.push_back("after_zero_delay"); };
    sched.ScheduleEvent({0}, Region::kReInactive, delayed);
  };
  sched.ScheduleEvent({0}, Region::kReactive, reactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "reactive");
  EXPECT_EQ(order[1], "after_zero_delay");
}

TEST(ReInactiveRegionSim, ReInactiveToReactiveIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* react1 = sched.GetEventPool().Acquire();
  react1->callback = [&]() {
    order.push_back("reactive1");
    auto* reinact = sched.GetEventPool().Acquire();
    reinact->callback = [&]() {
      order.push_back("reinactive");

      auto* react2 = sched.GetEventPool().Acquire();
      react2->callback = [&order]() { order.push_back("reactive2"); };
      sched.ScheduleEvent({0}, Region::kReactive, react2);
    };
    sched.ScheduleEvent({0}, Region::kReInactive, reinact);
  };
  sched.ScheduleEvent({0}, Region::kReactive, react1);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reactive1");
  EXPECT_EQ(order[1], "reinactive");
  EXPECT_EQ(order[2], "reactive2");
}

TEST(ReInactiveRegionSim, ChainedZeroDelayIteration) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto log_reinactive2 = [&order]() { order.push_back("reinactive2"); };
  auto do_reactive2 = [&]() {
    order.push_back("reactive2");
    auto* reinact2 = sched.GetEventPool().Acquire();
    reinact2->callback = log_reinactive2;
    sched.ScheduleEvent({0}, Region::kReInactive, reinact2);
  };

  auto do_reinactive1 = [&]() {
    order.push_back("reinactive1");
    auto* react2 = sched.GetEventPool().Acquire();
    react2->callback = do_reactive2;
    sched.ScheduleEvent({0}, Region::kReactive, react2);
  };

  auto* react1 = sched.GetEventPool().Acquire();
  react1->callback = [&]() {
    order.push_back("reactive1");
    auto* reinact1 = sched.GetEventPool().Acquire();
    reinact1->callback = do_reinactive1;
    sched.ScheduleEvent({0}, Region::kReInactive, reinact1);
  };
  sched.ScheduleEvent({0}, Region::kReactive, react1);

  sched.Run();
  std::vector<std::string> expected = {"reactive1", "reinactive1", "reactive2",
                                       "reinactive2"};
  EXPECT_EQ(order, expected);
}

TEST(ReInactiveRegionSim, ReInactiveExecutesBeforeReNBA) {
  VerifyTwoRegionOrder({Region::kReInactive, "reinactive"},
                       {Region::kReNBA, "renba"});
}

TEST(ReInactiveRegionSim, ReInactiveEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kReInactive);
}

TEST(ReInactiveRegionSim, ReInactiveRegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReInactive, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}
// §4.4.2.7 ¶2 sentence 2: "The Re-Inactive region is the reactive region set
// dual of the Inactive region (see 4.4.2.3)." The named production helper
// Scheduler::ReactiveSetDualOf maps the active-set anchor Region::kInactive
// to its reactive-set counterpart Region::kReInactive, codifying the
// §4.4.2.7 dual as a one-to-one map between the §4.4.2.3 and §4.4.2.7
// anchor regions. Any non-anchor input returns kCOUNT so the dual stays
// one-to-one. The classifier-symmetry check confirms each anchor sits in
// its set (Inactive in the active set, Re-Inactive in the reactive set),
// matching the §4.4.2.7 framing of the duality.
TEST(ReInactiveRegionSim, ReInactiveIsReactiveSetDualOfInactive) {
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kInactive),
            Region::kReInactive);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kReInactive),
            Region::kCOUNT);

  EXPECT_TRUE(IsActiveRegionSet(Region::kInactive));
  EXPECT_TRUE(IsReactiveRegionSet(Region::kReInactive));
}

// §4.4.2.7 ¶2 sentence 1: "If events are being executed in the reactive
// region set, an explicit #0 delay control requires the process to be
// suspended and an event to be scheduled into the Re-Inactive region of the
// current time slot so that the process can be resumed in the next
// Re-Inactive to Reactive iteration." The production code that applies this
// rule is DelayAwaiter::SelectDelayRegion: when the awaited delay is 0 and
// ctx.IsReactiveContext() is true, it returns Region::kReInactive, then
// await_suspend schedules the resume event there. Driving the rule from a
// `program` initial — which the lowerer marks as a reactive process — is the
// only path that exercises the IsReactiveContext() branch of SelectDelayRegion.
// The NBA `b <= 8'd9` queues an event into Re-NBA (the reactive-set NBA
// region); Re-Inactive runs before Re-NBA within the reactive set, so when
// the process resumes from the #0 the post-resume read of `b` must observe 0
// (Re-NBA has not yet fired). A misroute past Re-NBA — or any region after
// it — would let the NBA update apply first and the resume would observe 9.
// The `done = #0 8'd1;` form also drives the assignment through the same
// DelayAwaiter; observing `done == 1` confirms the resume actually fires
// (process not stranded), and `t == 0` confirms the resume stays in the
// current time slot, satisfying "next Re-Inactive to Reactive iteration".
TEST(ReInactiveRegionSim,
     ZeroDelayFromReactiveContextRoutesToReInactiveAndResumesInSameSlot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] b, snap, done;\n"
      "  program p;\n"
      "    initial begin\n"
      "      b = 8'd0;\n"
      "      snap = 8'd0;\n"
      "      b <= 8'd9;\n"
      "      done = #0 8'd1;\n"
      "      snap = b;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("done")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 9u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

