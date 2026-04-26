#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

// §4.9.3 atom: a blocking assignment with intra-assignment delay computes the
// right-hand side using the *current* values, before the process is suspended.
// Observed by `dst = #10 src;` where a parallel initial mutates `src` during
// the suspension — `ExecBlockingAssignTimed` calls `EvalExpr(stmt->rhs, ...)`
// before `co_await DelayAwaiter`, so the captured value must be the pre-mutation
// `src`. A resume-time RHS evaluation would yield the post-mutation value.
TEST(BlockingAssignSchedulingSim, RhsComputedUsingCurrentValuesAtSuspend) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, dst;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    dst = #10 src;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("src")->value.ToUint64(), 99u);
}

// §4.9.3 atom A1 edge case (plural "current values"): when the RHS expression
// has multiple source operands, every operand must be captured at suspend
// time, not just one. `ExecBlockingAssignTimed` evaluates the RHS expression
// as a whole through `EvalExpr` before `co_await DelayAwaiter`, so an
// `a + b` RHS reads both operands at the suspend tick. Observed by mutating
// `a` and `b` at distinct times during the delay window — the captured RHS
// must equal the pre-mutation `a + b`. A single-operand snapshot would let
// the unmutated operand "drift" with its source variable; a resume-time
// re-evaluation would yield the post-mutation sum.
TEST(BlockingAssignSchedulingSim, RhsMultipleSourcesAllCapturedAtSuspend) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, dst;\n"
      "  initial begin\n"
      "    a = 8'd3;\n"
      "    b = 8'd4;\n"
      "    dst = #10 (a + b);\n"
      "  end\n"
      "  initial begin\n"
      "    #2 a = 8'd99;\n"
      "    #5 b = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 99u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 11u);
}

// §4.9.3 atom: the executing process is suspended and scheduled as a future
// event at `current_time + delay`. Observed by running a single `b = #10 99;`
// — `DelayAwaiter::await_suspend` schedules the resume callback at tick 10, so
// `Scheduler::Run` must advance `CurrentTime` to 10 in order for the
// assignment to land. A failure to suspend (or to schedule for the future)
// would leave `b` at its default and `CurrentTime` at 0.
TEST(BlockingAssignSchedulingSim, ProcessSuspendsAndScheduledAsFutureEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    b = #10 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

// §4.9.3 atom: when the delay is zero in an Active (non-Reactive) context, the
// process is scheduled as an Inactive event for the current time.
// `DelayAwaiter::SelectDelayRegion` returns `Region::kInactive` for this case.
// Observed by issuing `b <= 7;` (NBA at t=0) immediately followed by
// `#0 done = 1;` and capturing `b` after the resume. Inactive runs *before*
// NBA within the active set, so the post-resume `snap` reads `b` as 0
// (NBA hasn't fired). If the production routed to a Reactive-set region (or to
// any region after NBA), the resume would observe `b == 7` — i.e. `snap == 7`.
TEST(BlockingAssignSchedulingSim, ZeroDelayFromActiveContextRoutesToInactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b, snap, done;\n"
      "  initial begin\n"
      "    b = 8'd0;\n"
      "    snap = 8'd0;\n"
      "    b <= 8'd7;\n"
      "    done = #0 8'd1;\n"
      "    snap = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("done")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

// §4.9.3 atom: when the delay is zero and the blocking assignment runs from a
// Reactive region (e.g., a `program` initial), the process is scheduled as a
// Re-Inactive event. `DelayAwaiter::SelectDelayRegion` returns
// `Region::kReInactive` when `IsReactiveContext()` is true and the delay is 0.
// Observed by a `program` initial that issues `b <= 7;` (which goes to ReNBA
// per `ExecNonblockingAssignImpl`'s reactive-region routing) then `#0 ...;`
// — Re-Inactive runs before ReNBA within the reactive set, so the post-resume
// `snap` reads `b == 0`. Misrouting to the active-set Inactive (or any region
// after ReNBA) would drain ReNBA first and leave `snap == 7`.
TEST(BlockingAssignSchedulingSim, ZeroDelayFromReactiveContextRoutesToReInactive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] b, snap, done;\n"
      "  program p;\n"
      "    initial begin\n"
      "      b = 8'd0;\n"
      "      snap = 8'd0;\n"
      "      b <= 8'd7;\n"
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
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
}

// §4.9.3 atom: when the process resumes, the assignment to the LHS *enables
// any events based upon the update of the LHS*. After `co_await DelayAwaiter`,
// `PerformBlockingAssign` writes `lhs` and notifies its watchers. Observed by
// pairing `sig = #5 8'd1;` with an `always @(sig) trig = 8'd1;` — the always
// block must fire at t=5 because the resume's LHS write triggered its
// sensitivity. If the resume only stored the value without notifying watchers,
// `trig` would remain at 0.
TEST(BlockingAssignSchedulingSim, ResumeEnablesEventsOnLhsUpdate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sig, trig;\n"
      "  initial begin\n"
      "    sig = 8'd0;\n"
      "    trig = 8'd0;\n"
      "    sig = #5 8'd1;\n"
      "  end\n"
      "  always @(sig) trig = 8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sig")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("trig")->value.ToUint64(), 1u);
}

// §4.9.3 atom: the values at the time the process resumes are used to
// determine the target(s). `PerformBlockingAssign(stmt->lhs, rhs_val, ...)` is
// invoked after the await, so any index expression in the LHS resolves at
// resume time. Observed by `mem[idx] = #10 8'hCC;` where a parallel initial
// flips `idx` from 0 to 1 during the delay — the resume must write to
// `mem[1]`, not `mem[0]`. A suspend-time target binding would put 0xCC in
// `mem[0]` and leave `mem[1]` at 0.
TEST(BlockingAssignSchedulingSim, TargetEvaluatedAtResumeTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    mem[0] = 8'd0;\n"
      "    mem[1] = 8'd0;\n"
      "    idx = 0;\n"
      "    mem[idx] = #10 8'hCC;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 idx = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mem[0]")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("mem[1]")->value.ToUint64(), 0xCCu);
}

// §4.9.3 atom: after the resume, execution may continue with the next
// sequential statement *or with other Active or Reactive events*. After
// `PerformBlockingAssign`, `ExecBlockingAssignTimed` returns `kDone` and the
// caller proceeds; meanwhile `Scheduler::Run` keeps draining other events at
// their scheduled times. Observed by combining (a) a sequential `c = 8'd2;`
// after the delayed `b = #10 8'd1;` with (b) a parallel initial that mutates
// `parallel_marker` at t=5 during the suspension. All three writes must land:
// suspending wholesale would block `parallel_marker`; failing to resume would
// leave `b` and `c` unset.
TEST(BlockingAssignSchedulingSim, ContinuesWithNextStatementAndOtherEvents) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b, c, parallel_marker;\n"
      "  initial begin\n"
      "    b = 8'd0;\n"
      "    c = 8'd0;\n"
      "    parallel_marker = 8'd0;\n"
      "    b = #10 8'd1;\n"
      "    c = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 parallel_marker = 8'd9;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("parallel_marker")->value.ToUint64(), 9u);
}
