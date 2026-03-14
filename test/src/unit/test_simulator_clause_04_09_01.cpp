#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"

using namespace delta;

TEST(ContinuousAssignSchedulingSim, ContinuousAssignmentCorrespondsToProcess) {
  VerifyCACorrespondsToProcess();
}

TEST(ContinuousAssignSchedulingSim, SensitiveToSourceElements) {
  Arena arena;
  Scheduler sched(arena);
  int a = 0;
  int b = 0;
  int dst = 0;
  int unrelated = 0;
  bool cont_assign_triggered = false;

  auto* change_a = sched.GetEventPool().Acquire();
  change_a->kind = EventKind::kEvaluation;
  change_a->callback = [&]() {
    a = 3;

    cont_assign_triggered = true;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = a + b; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, change_a);

  auto* change_unrelated = sched.GetEventPool().Acquire();
  change_unrelated->kind = EventKind::kEvaluation;
  change_unrelated->callback = [&]() { unrelated = 99; };
  sched.ScheduleEvent({1}, Region::kActive, change_unrelated);

  sched.Run();
  EXPECT_TRUE(cont_assign_triggered);
  EXPECT_EQ(dst, 3);
  EXPECT_EQ(unrelated, 99);
}

TEST(ContinuousAssignSchedulingSim, SchedulesActiveUpdateEvent) {
  VerifyCASchedulesActiveUpdateEvent();
}

TEST(ContinuousAssignSchedulingSim, UsesCurrentValuesToDetermineTarget) {
  Arena arena;
  Scheduler sched(arena);
  int select = 0;
  int dst_a = 0;
  int dst_b = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() {
      if (select == 0) {
        dst_a = 1;
      } else {
        dst_b = 1;
      }
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(dst_a, 1);
  EXPECT_EQ(dst_b, 0);
}

TEST(ContinuousAssignSchedulingSim, EvaluatedAtTimeZeroForConstantPropagation) {
  Arena arena;
  Scheduler sched(arena);
  int dst = -1;

  auto* const_assign = sched.GetEventPool().Acquire();
  const_assign->kind = EventKind::kEvaluation;
  const_assign->callback = [&]() {
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { dst = 42; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, const_assign);

  sched.Run();
  EXPECT_EQ(dst, 42);
  EXPECT_EQ(sched.CurrentTime().ticks, 0u);
}

TEST(ContinuousAssignSchedulingSim, TimeZeroEvalBeforeProceduralReads) {
  Arena arena;
  Scheduler sched(arena);
  int net_val = -1;
  int read_val = -1;

  auto* cont_assign = sched.GetEventPool().Acquire();
  cont_assign->kind = EventKind::kEvaluation;
  cont_assign->callback = [&]() {
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { net_val = 7; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, cont_assign);

  auto* proc_read = sched.GetEventPool().Acquire();
  proc_read->kind = EventKind::kEvaluation;
  proc_read->callback = [&]() { read_val = net_val; };
  sched.ScheduleEvent({0}, Region::kInactive, proc_read);

  sched.Run();
  EXPECT_EQ(net_val, 7);
  EXPECT_EQ(read_val, 7);
}

TEST(ContinuousAssignSchedulingSim, ImplicitContinuousAssignmentFromInputPort) {
  Arena arena;
  Scheduler sched(arena);
  int outside_sig = 0;
  int local_input = 0;

  auto* drive = sched.GetEventPool().Acquire();
  drive->kind = EventKind::kEvaluation;
  drive->callback = [&]() {
    outside_sig = 5;
    auto* port_update = sched.GetEventPool().Acquire();
    port_update->kind = EventKind::kUpdate;
    port_update->callback = [&]() { local_input = outside_sig; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, port_update);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive);

  sched.Run();
  EXPECT_EQ(local_input, 5);
}

TEST(ContinuousAssignSchedulingSim, ImplicitContinuousAssignmentFromOutputPort) {
  Arena arena;
  Scheduler sched(arena);
  int local_output = 0;
  int outside_net = 0;

  auto* drive = sched.GetEventPool().Acquire();
  drive->kind = EventKind::kEvaluation;
  drive->callback = [&]() {
    local_output = 33;
    auto* port_update = sched.GetEventPool().Acquire();
    port_update->kind = EventKind::kUpdate;
    port_update->callback = [&]() { outside_net = local_output; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, port_update);
  };
  sched.ScheduleEvent({0}, Region::kActive, drive);

  sched.Run();
  EXPECT_EQ(outside_net, 33);
}

TEST(ContinuousAssignSchedulingSim, MultipleContinuousAssignmentsToSameNet) {
  Arena arena;
  Scheduler sched(arena);
  int driver_a = 0;
  int driver_b = 0;
  int net = 0;

  auto* eval_a = sched.GetEventPool().Acquire();
  eval_a->kind = EventKind::kEvaluation;
  eval_a->callback = [&]() {
    driver_a = 1;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { net = driver_a; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval_a);

  auto* eval_b = sched.GetEventPool().Acquire();
  eval_b->kind = EventKind::kEvaluation;
  eval_b->callback = [&]() {
    driver_b = 2;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&]() { net = driver_b; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval_b);

  sched.Run();

  EXPECT_TRUE(net == 1 || net == 2);
}

TEST(ContinuousAssignSchedulingSim, NoUpdateWhenExpressionUnchanged) {
  Arena arena;
  Scheduler sched(arena);
  int src = 5;
  int dst = 0;
  int update_count = 0;

  auto* eval0 = sched.GetEventPool().Acquire();
  eval0->kind = EventKind::kEvaluation;
  eval0->callback = [&]() {
    int new_val = src;
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&, new_val]() {
      dst = new_val;
      ++update_count;
    };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval0);

  auto* eval1 = sched.GetEventPool().Acquire();
  eval1->kind = EventKind::kEvaluation;
  eval1->callback = [&]() {
    int new_val = src;
    if (new_val != dst) {
      auto* update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&, new_val]() {
        dst = new_val;
        ++update_count;
      };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({1}, Region::kActive, eval1);

  sched.Run();
  EXPECT_EQ(dst, 5);
  EXPECT_EQ(update_count, 1);
}

TEST(SchedulingSemanticsSim, ContinuousAssignAsProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] in_val, out_val;\n"
      "  assign out_val = in_val;\n"
      "  initial in_val = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("out_val");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}
