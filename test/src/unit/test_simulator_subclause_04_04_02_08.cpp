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

// D1 (Re-NBA drains after all Re-Inactive) is covered by the stronger
// four-region order test below and by the mid-drain test, which asserts the
// same reinactive<renba relation over both statically and dynamically
// scheduled Re-Inactive events; standalone pairwise/batch variants were
// redundant and were removed (mirrors the §4.4.2.4 NBA suite dedup).

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

TEST(ReNbaRegionSim,
     NonblockingAssignFromReactiveSetWithDelaySchedulesReNBALater) {
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

// D2, array-concatenation nonblocking-assign form: an unpacked-array target
// assigned a concatenation from within a reactive-set process (program block)
// still defers its per-element updates to the Re-NBA region. Exercises the
// distinct array-concat routing site in production. Discriminates deferral: a
// blocking write to mem[0] after the nonblocking assign is overwritten by the
// deferred Re-NBA update (mem[0] ends at 10, not the later blocking 7).
TEST(ReNbaRegionSim,
     ArrayConcatNonblockingAssignFromReactiveSetSchedulesReNBA) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] mem [0:1];\n"
      "  program p;\n"
      "    initial begin\n"
      "      mem[0] = 8'd1;\n"
      "      mem[1] = 8'd2;\n"
      "      mem <= {8'd10, 8'd20};\n"
      "      mem[0] = 8'd7;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mem[0]")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("mem[1]")->value.ToUint64(), 20u);
}

// D2, streaming-concatenation nonblocking-assign form (§11.4.14.3): a streaming
// target of a nonblocking assign executed in a reactive-set process defers its
// reverse (unpack) writes to the Re-NBA region. Exercises the distinct
// streaming routing site in production. Discriminates deferral: the later
// blocking write to `a` is overwritten by the deferred Re-NBA unpack, so `a`
// ends at the unpacked 0xAB rather than the blocking 9.
TEST(ReNbaRegionSim,
     StreamingConcatNonblockingAssignFromReactiveSetSchedulesReNBA) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  program p;\n"
      "    initial begin\n"
      "      a = 8'd1;\n"
      "      {>> {a, b}} <= 16'hABCD;\n"
      "      a = 8'd9;\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xCDu);
}

TEST(ReNbaRegionSim, ReNBAIsReactiveSetDualOfNBA) {
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kNBA), Region::kReNBA);
  EXPECT_EQ(Scheduler::ReactiveSetDualOf(Region::kReNBA), Region::kCOUNT);

  EXPECT_TRUE(IsActiveRegionSet(Region::kNBA));
  EXPECT_TRUE(IsReactiveRegionSet(Region::kReNBA));
}
