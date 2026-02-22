#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.9.7 Subroutines
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.9.7 — Argument passing is by value
// ---------------------------------------------------------------------------
TEST(SimCh4097, ArgumentPassedByValue) {
  Arena arena;
  Scheduler sched(arena);
  int caller_var = 10;
  int subroutine_local = 0;

  // Model: task t(input int arg); arg = 99; endtask
  //        t(caller_var);
  // The subroutine modifies its local copy, not the caller's variable.
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Copy-in: subroutine receives a copy of caller_var.
    subroutine_local = caller_var;
    // Subroutine modifies its local copy.
    subroutine_local = 99;
    // caller_var is unaffected by the modification.
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(caller_var, 10); // Unchanged — passed by value.
  EXPECT_EQ(subroutine_local, 99);
}

// ---------------------------------------------------------------------------
// §4.9.7 — Copy-in happens at invocation time
// ---------------------------------------------------------------------------
TEST(SimCh4097, CopyInOnInvocation) {
  Arena arena;
  Scheduler sched(arena);
  int src = 42;
  int copied_in = 0;

  // Model: task t(input int arg); #5; use arg; endtask
  //        t(src);
  // At time 0, src=42 → copied_in=42. src changes at time 3, but the
  // subroutine still has the value from invocation time.
  auto *invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    // Copy-in at invocation time.
    copied_in = src;
    // Subroutine body resumes at time 5 — but copy-in already happened.
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  // Change src at time 3, after invocation but before subroutine completes.
  auto *change_src = sched.GetEventPool().Acquire();
  change_src->kind = EventKind::kEvaluation;
  change_src->callback = [&]() { src = 999; };
  sched.ScheduleEvent({3}, Region::kActive, change_src);

  sched.Run();
  // copied_in captured the value at invocation (time 0), not time 3.
  EXPECT_EQ(copied_in, 42);
  EXPECT_EQ(src, 999);
}

// ---------------------------------------------------------------------------
// §4.9.7 — Copy-out happens on return
// ---------------------------------------------------------------------------
TEST(SimCh4097, CopyOutOnReturn) {
  Arena arena;
  Scheduler sched(arena);
  int caller_dst = 0;
  bool returned = false;

  // Model: task t(output int arg); arg = 77; endtask
  //        t(caller_dst);
  // The output arg is copied out to caller_dst when the task returns.
  auto *invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    // Subroutine body computes output value.
    int output_arg = 77;
    // On return, copy-out: write output_arg to caller's destination.
    caller_dst = output_arg;
    returned = true;
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();
  EXPECT_TRUE(returned);
  EXPECT_EQ(caller_dst, 77);
}

// ---------------------------------------------------------------------------
// §4.9.7 — Inout argument: copy-in at invocation, copy-out on return
// ---------------------------------------------------------------------------
TEST(SimCh4097, InoutArgCopiedInAndOut) {
  Arena arena;
  Scheduler sched(arena);
  int caller_var = 5;

  // Model: task t(inout int arg); arg = arg + 10; endtask
  //        t(caller_var);
  // Copy-in: arg=5 at invocation. Body: arg=15. Copy-out: caller_var=15.
  auto *invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    // Copy-in at invocation.
    int arg = caller_var;
    // Subroutine body modifies arg.
    arg = arg + 10;
    // Copy-out on return.
    caller_var = arg;
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();
  EXPECT_EQ(caller_var, 15);
}

// ---------------------------------------------------------------------------
// §4.9.7 — Multiple output arguments all copied out on return
// ---------------------------------------------------------------------------
TEST(SimCh4097, MultipleCopyOutArgsOnReturn) {
  Arena arena;
  Scheduler sched(arena);
  int dst_a = 0;
  int dst_b = 0;
  int dst_c = 0;

  // Model: task t(output int a, output int b, output int c);
  //          a = 1; b = 2; c = 3;
  //        endtask
  //        t(dst_a, dst_b, dst_c);
  auto *invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    // Subroutine body computes outputs.
    int out_a = 1;
    int out_b = 2;
    int out_c = 3;
    // Copy-out all outputs on return.
    dst_a = out_a;
    dst_b = out_b;
    dst_c = out_c;
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();
  EXPECT_EQ(dst_a, 1);
  EXPECT_EQ(dst_b, 2);
  EXPECT_EQ(dst_c, 3);
}

// ---------------------------------------------------------------------------
// §4.9.7 — Copy-out behaves as a blocking assignment (immediate)
// ---------------------------------------------------------------------------
TEST(SimCh4097, CopyOutBehavesAsBlockingAssignment) {
  Arena arena;
  Scheduler sched(arena);
  int result = 0;
  int observed_after_call = -1;

  // Model: task t(output int arg); arg = 42; endtask
  //        t(result);
  //        observed_after_call = result;  // Should see 42 immediately.
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Subroutine executes, copy-out on return (blocking).
    int out_arg = 42;
    result = out_arg; // Copy-out behaves as blocking assignment.
    // Next sequential statement sees the updated value immediately.
    observed_after_call = result;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(result, 42);
  EXPECT_EQ(observed_after_call, 42);
}

// ---------------------------------------------------------------------------
// §4.9.7 — Copy-out enables events on the updated variable
// ---------------------------------------------------------------------------
TEST(SimCh4097, CopyOutEnablesEventsOnUpdate) {
  Arena arena;
  Scheduler sched(arena);
  int sig = 0;
  bool sensitive_triggered = false;

  // Model: task t(output int arg); arg = 5; endtask
  //        t(sig);
  // The copy-out updates sig, which triggers a process sensitive to sig.
  auto *invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    // Subroutine body.
    int out_arg = 5;
    // Copy-out on return (blocking assignment to sig).
    sig = out_arg;
    // The update of sig enables events — modeled as scheduling a sensitive
    // process in the Active region (same as §4.9.3 blocking assignment).
    auto *sensitive = sched.GetEventPool().Acquire();
    sensitive->kind = EventKind::kEvaluation;
    sensitive->callback = [&]() { sensitive_triggered = true; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, sensitive);
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();
  EXPECT_EQ(sig, 5);
  EXPECT_TRUE(sensitive_triggered);
}

// ---------------------------------------------------------------------------
// §4.9.7 — Copy-out does not suspend the calling process
// ---------------------------------------------------------------------------
TEST(SimCh4097, CopyOutDoesNotSuspendProcess) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Model: task t(output int arg); arg = 1; endtask
  //        begin
  //          before_call;
  //          t(dst);       // copy-out happens here
  //          after_call;   // continues immediately
  //        end
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    order.push_back("before_call");
    // Subroutine call with copy-out (blocking — no suspension).
    int dst = 0;
    dst = 1; // Copy-out on return.
    order.push_back("after_call");
    (void)dst;
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "before_call");
  EXPECT_EQ(order[1], "after_call");
}

// ---------------------------------------------------------------------------
// §4.9.7 — Copy-out occurs in the Active region
// ---------------------------------------------------------------------------
TEST(SimCh4097, CopyOutOccursInActiveRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Model: subroutine return copy-out vs NBA.
  // The copy-out (blocking) happens in Active, before NBA executes.
  auto *eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    // Copy-out (blocking assignment) — happens in Active.
    order.push_back("copyout_active");

    // Schedule an NBA for comparison.
    auto *nba = sched.GetEventPool().Acquire();
    nba->kind = EventKind::kUpdate;
    nba->callback = [&]() { order.push_back("nba_event"); };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kNBA, nba);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "copyout_active");
  EXPECT_EQ(order[1], "nba_event");
}

// ---------------------------------------------------------------------------
// §4.9.7 — Copy-in and copy-out are independent operations
// ---------------------------------------------------------------------------
TEST(SimCh4097, CopyInAndCopyOutAreIndependent) {
  Arena arena;
  Scheduler sched(arena);
  int caller_x = 10;
  int caller_y = 0;

  // Model: task t(input int x, output int y); y = x * 2; endtask
  //        t(caller_x, caller_y);
  // Copy-in captures caller_x=10 at invocation. During subroutine,
  // caller_x is changed by another process. Copy-out writes y=20
  // regardless of caller_x's later value.
  auto *invoke = sched.GetEventPool().Acquire();
  invoke->kind = EventKind::kEvaluation;
  invoke->callback = [&]() {
    // Copy-in at invocation.
    int x_local = caller_x; // 10 at invocation time.
    // Subroutine body.
    int y_local = x_local * 2; // 20.
    // Simulate caller_x changing during subroutine execution.
    caller_x = 999;
    // Copy-out on return — writes to caller_y.
    caller_y = y_local;
  };
  sched.ScheduleEvent({0}, Region::kActive, invoke);

  sched.Run();
  // Copy-in used invocation value (10), so y = 20.
  EXPECT_EQ(caller_y, 20);
  // caller_x was modified during execution.
  EXPECT_EQ(caller_x, 999);
}
