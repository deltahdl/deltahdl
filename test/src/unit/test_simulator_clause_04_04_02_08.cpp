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

TEST(ReNbaRegionSim, ReNBAExecutesAfterReInactive) {
  VerifyTwoRegionOrder({Region::kReInactive, "reinactive"},
                       {Region::kReNBA, "renba"});
}

TEST(ReNbaRegionSim, AllReInactiveEventsCompleteBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  for (int i = 0; i < 3; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, i]() {
      order.push_back("reinactive" + std::to_string(i));
    };
    sched.ScheduleEvent({0}, Region::kReInactive, ev);
  }

  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { order.push_back("renba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);

  EXPECT_EQ(order[3], "renba");
}

TEST(ReNbaRegionSim, ReNBAToReactiveIteration) {
  VerifyIterationChain(Region::kReactive, "reactive", Region::kReNBA, "renba");
}

TEST(ReNbaRegionSim, ReNBAExecutesAfterReactiveAndReInactiveBeforePostReNBA) {
  VerifyFourRegionOrder(
      {Region::kReactive, "reactive"}, {Region::kReInactive, "reinactive"},
      {Region::kReNBA, "renba"}, {Region::kPostReNBA, "post_renba"});
}

TEST(ReNbaRegionSim, ReNBAEventsAcrossMultipleTimeSlots) {
  VerifyEventsAcrossTimeSlots(Region::kReNBA);
}

TEST(ReNbaRegionSim, ReNBARegionHoldsMultipleEvents) {
  Arena arena;
  Scheduler sched(arena);
  int count = 0;

  for (int i = 0; i < 5; ++i) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&]() { count++; };
    sched.ScheduleEvent({0}, Region::kReNBA, ev);
  }

  sched.Run();
  EXPECT_EQ(count, 5);
}

// §4.4.2.8 ¶1: "after **all** the Re-Inactive events are processed" —
// including Re-Inactive events scheduled into the same time slot from inside
// another Re-Inactive callback. Distinct from
// AllReInactiveEventsCompleteBeforeReNBA, which pre-queues every Re-Inactive
// before Run() and so never exercises the reentrant-push path through
// DrainQueue's `while (!queue.empty())` loop. If that loop snapshotted queue
// length on entry (instead of testing emptiness on each pop), the mid-drain
// reinactive2 would defer past Re-NBA and the observed order would put "renba"
// before "reinactive2".
TEST(ReNbaRegionSim, ReInactivesScheduledDuringDrainRunBeforeReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* reinact1 = sched.GetEventPool().Acquire();
  reinact1->callback = [&]() {
    order.push_back("reinactive1");
    auto* reinact2 = sched.GetEventPool().Acquire();
    reinact2->callback = [&]() { order.push_back("reinactive2"); };
    sched.ScheduleEvent({0}, Region::kReInactive, reinact2);
  };
  sched.ScheduleEvent({0}, Region::kReInactive, reinact1);

  auto* renba = sched.GetEventPool().Acquire();
  renba->callback = [&]() { order.push_back("renba"); };
  sched.ScheduleEvent({0}, Region::kReNBA, renba);

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reinactive1");
  EXPECT_EQ(order[1], "reinactive2");
  EXPECT_EQ(order[2], "renba");
}

// §4.4.2.8 ¶2 sentence 1: "If events are being executed in the reactive
// region set, a nonblocking assignment creates an event in the Re-NBA update
// region scheduled for the current ... simulation time." Drives the rule
// through the real lowering path: a `program` initial is marked reactive by
// the lowerer, so the `a <= 8'd99` inside it routes through
// statement_assign_core's `ctx.IsReactiveContext() ? Region::kReNBA :
// Region::kNBA` decision and queues into Re-NBA at the current time. The
// reactive region set drains Reactive → Re-Inactive → Re-NBA, so within the
// same time slot `b = a + 8'd2` (blocking, in Reactive) reads the pre-Re-NBA
// value (1, giving 3) and `a = a + 8'd5` continues the Reactive chain. Only
// after the reactive set drains does the Re-NBA event fire and overwrite `a`
// with 99. Final `a == 99` proves the assignment was deferred (i.e., the
// scheduler placed it in Re-NBA rather than applying it inline); final
// `b == 3` proves the deferral happened past the same-slot Reactive reads.
TEST(ReNbaRegionSim, NonblockingAssignFromReactiveSetSchedulesReNBA) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  program p;\n"
      "    initial begin\n"
      "      a = 8'd1;\n"
      "      b = a + 8'd2;\n"
      "      a <= 8'd99;\n"
      "      a = a + 8'd5;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 99u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 3u);
}

// §4.4.2.8 ¶2 sentence 1: "... scheduled for the current or a later
// simulation time." Lowering `b <= #5 8'd99` inside a `program` initial
// enqueues the Re-NBA event at t=5; the scheduler advances time before
// draining Re-NBA, so on completion the simulator's current time reflects the
// deferred slot. Mirrors the §4.4.2.4 NBA later-time test but exercises the
// reactive-context branch of statement_assign_core's region selection.
TEST(ReNbaRegionSim, NonblockingAssignFromReactiveSetWithDelaySchedulesReNBALater) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] b;\n"
      "  program p;\n"
      "    initial b <= #5 8'd99;\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}

// §4.4.2.8 ¶2 sentence 2: "The Re-NBA region is the reactive region set dual
// of the NBA region (see 4.4.2.4)." The named production helper
// Scheduler::ReactiveSetDualOf maps the active-set anchor Region::kNBA to its
// reactive-set counterpart Region::kReNBA, codifying the §4.4.2.8 dual as a
// one-to-one map between the §4.4.2.4 and §4.4.2.8 anchor regions. Any
// non-anchor input (including kReNBA itself) returns kCOUNT so the dual stays
// one-to-one. The classifier-symmetry check confirms each anchor sits in its
// set (NBA in the active set, Re-NBA in the reactive set), matching the
// §4.4.2.8 framing of the duality.
TEST(ReNbaRegionSim, ReNBAIsReactiveSetDualOfNBA) {
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kNBA), Region::kReNBA);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kReNBA), Region::kCOUNT);

  EXPECT_TRUE(IsActiveRegionSet(Region::kNBA));
  EXPECT_TRUE(IsReactiveRegionSet(Region::kReNBA));
}
