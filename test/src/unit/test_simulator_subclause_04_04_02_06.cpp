#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler_event.h"
#include "simulator/checker_scheduling_semantics.h"
#include "simulator/scheduler.h"
#include "simulator/sva_engine_queues.h"
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

  EXPECT_EQ(seen->value.ToUint64(), 42u);
  EXPECT_EQ(shared->value.ToUint64(), 99u);
}

TEST(ReactiveRegionSim, CheckerBlockingAssignmentHomeIsReactive) {
  EXPECT_EQ(HomeRegionForCheckerStatement(CheckerStatementKind::kBlocking),
            Region::kReactive);
  EXPECT_NE(HomeRegionForCheckerStatement(
                CheckerStatementKind::kCheckerVariableNonblocking),
            Region::kReactive);
}

TEST(ReactiveRegionSim, ConcurrentAssertionActionBlockHomeIsReactive) {
  EXPECT_EQ(ConcurrentAssertActionRegion(), Region::kReactive);
}

TEST(ReactiveRegionSim,
     ConcurrentAssertionActionIsNotSeenFromTheInactiveRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk = 0;\n"
      "  int flag = 0;\n"
      "  int saw = 99;\n"
      "  always @(posedge clk) assert property (1'b1) flag = 1;\n"
      "  always @(posedge clk) begin\n"
      "    #0;\n"
      "    saw = flag;\n"
      "  end\n"
      "  initial #5 clk = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* saw = f.ctx.FindVariable("saw");
  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(saw, nullptr);
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(saw->value.ToUint64(), 0u);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
}

TEST(ReactiveRegionSim,
     ConcurrentAssertionActionIsSeenFromTheReInactiveRegion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk = 0;\n"
      "  int flag = 0;\n"
      "  int seen = 99;\n"
      "  always @(posedge clk) assert property (1'b1) flag = 1;\n"
      "  program p;\n"
      "    initial begin\n"
      "      @(posedge clk);\n"
      "      #0;\n"
      "      seen = flag;\n"
      "    end\n"
      "  endprogram\n"
      "  initial #5 clk = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* seen = f.ctx.FindVariable("seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_EQ(seen->value.ToUint64(), 1u);
}

TEST(ReactiveRegionSim,
     ConcurrentAssertionActionDelayDoesNotStallTheAssertion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk = 0;\n"
      "  int hits = 0;\n"
      "  always @(posedge clk)\n"
      "    assert property (@(posedge clk) 1'b1) #20 hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #40;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* hits = f.ctx.FindVariable("hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
}

static std::string RunEdgeReader(const std::string& reader) {
  SimFixture f;
  return RunCapture(
      "module top;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] q = 8'd0;\n"
      "  always @(posedge clk) q <= 8'd5;\n"
      "  initial #1 clk = 1;\n" +
          reader + "endmodule\n",
      f);
}

TEST(ReactiveRegionSim, ProgramWokenByAnEdgeSeesTheNonblockingUpdate) {
  EXPECT_EQ(RunEdgeReader("  program p;\n"
                          "    initial begin\n"
                          "      @(posedge clk);\n"
                          "      $display(\"program q=%0d\", q);\n"
                          "    end\n"
                          "  endprogram\n"),
            "program q=5\n");
}

TEST(ReactiveRegionSim, ModuleWokenByAnEdgeSeesTheValueBeforeTheUpdate) {
  EXPECT_EQ(RunEdgeReader("  initial begin\n"
                          "    @(posedge clk);\n"
                          "    $display(\"module q=%0d\", q);\n"
                          "  end\n"),
            "module q=0\n");
}
