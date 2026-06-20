

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(UniqueIfViolationSim, DeferredOverlapViolationReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, FlushClearsPendingViolations) {
  SimFixture f;

  Process proc;
  proc.kind = ProcessKind::kInitial;
  f.ctx.SetCurrentProcess(&proc);

  f.ctx.AddPendingViolation("test violation");
  ASSERT_EQ(proc.pending_violations.size(), 1u);

  f.ctx.FlushPendingViolations();
  EXPECT_TRUE(proc.pending_violations.empty());

  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(UniqueIfViolationSim, MatureReportsImmediately) {
  SimFixture f;

  Process proc;
  proc.kind = ProcessKind::kInitial;
  f.ctx.SetCurrentProcess(&proc);

  proc.pending_violations.push_back("mature test");
  f.ctx.MaturePendingViolations();

  EXPECT_TRUE(proc.pending_violations.empty());
  EXPECT_EQ(f.diag.WarningCount(), 1u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(UniqueIfViolationSim, MultipleViolationsMature) {
  SimFixture f;

  Process proc;
  proc.kind = ProcessKind::kInitial;
  f.ctx.SetCurrentProcess(&proc);

  f.ctx.AddPendingViolation("violation 1");
  f.ctx.AddPendingViolation("violation 2");
  ASSERT_EQ(proc.pending_violations.size(), 2u);

  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 2u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(UniqueIfViolationSim, FlushAfterPartialAccumulation) {
  SimFixture f;

  Process proc;
  proc.kind = ProcessKind::kInitial;
  f.ctx.SetCurrentProcess(&proc);

  f.ctx.AddPendingViolation("will be flushed");
  f.ctx.FlushPendingViolations();

  f.ctx.AddPendingViolation("will mature");

  f.scheduler.Run();

  EXPECT_EQ(f.diag.WarningCount(), 1u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(UniqueIfViolationSim, UniqueIfNoMatchNoElseWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    x = 8'd0;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, UniqueIfNoMatchWithElseNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, Unique0IfNoMatchNoElseNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    x = 8'd0;\n"
      "    unique0 if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, UniqueIfOverlapWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);

  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, Unique0IfOverlapWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique0 if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);

  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, UniqueIfSingleConditionNoOverlap) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd10;\n"
      "    else x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, Unique0IfMatchTakesBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique0 if (1) x = 8'd42;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, TwoProcessesBothViolateReportedTwice) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    unique if (1) y = 8'd3;\n"
      "    else if (1) y = 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_GE(f.diag.WarningCount(), 2u);
}

TEST(UniqueIfViolationSim, OneProcessViolatesOtherDoesNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    unique if (1) y = 8'd3;\n"
      "    else if (0) y = 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, FlushIsPerProcess) {
  SimFixture f;

  Process proc_a;
  proc_a.kind = ProcessKind::kInitial;
  Process proc_b;
  proc_b.kind = ProcessKind::kInitial;

  f.ctx.SetCurrentProcess(&proc_a);
  f.ctx.AddPendingViolation("proc_a violation");

  f.ctx.SetCurrentProcess(&proc_b);
  f.ctx.AddPendingViolation("proc_b violation");

  f.ctx.SetCurrentProcess(&proc_a);
  f.ctx.FlushPendingViolations();

  EXPECT_TRUE(proc_a.pending_violations.empty());
  EXPECT_EQ(proc_b.pending_violations.size(), 1u);

  f.scheduler.Run();

  EXPECT_EQ(f.diag.WarningCount(), 1u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(UniqueIfViolationSim, TwoProcessesNoMatchBothReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    unique if (0) x = 8'd1;\n"
      "    else if (0) x = 8'd2;\n"
      "  end\n"
      "  initial begin\n"
      "    y = 8'd0;\n"
      "    unique if (0) y = 8'd3;\n"
      "    else if (0) y = 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_GE(f.diag.WarningCount(), 2u);
}

TEST(UniqueIfViolationSim, UniqueIfThreeBranchesOneMatchNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else if (a == 8'd2) x = 8'd30;\n"
      "    else x = 8'd40;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, AlwaysCombRetriggerFlushesPendingViolation) {
  // §12.4.2.1: an always_comb procedure that accumulates a unique-if violation
  // and is then resumed by a transition on a dependent signal reaches a flush
  // point on that resume. Here the first evaluation sees a==1 and b==1, so both
  // branch conditions match and a violation is queued. The nonblocking update
  // of b re-triggers the procedure within the same time step; on resume the
  // pending violation is flushed before the Observed region can mature it, so
  // nothing is reported. Without the flush the stale violation would mature and
  // produce a warning.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_comb begin\n"
      "    unique if (a) z = 8'd1;\n"
      "    else if (b) z = 8'd2;\n"
      "    else z = 8'd0;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, EventControlFlushesPendingViolation) {
  // §12.4.2.1: a process that accumulates a unique-if violation and then
  // suspends on an event control reaches a flush point when it resumes in the
  // same time step (before the Observed region matures the report), so the
  // pending violation is discarded and never reported.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "    @e;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    -> e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, WaitStatementFlushesPendingViolation) {
  // §12.4.2.1: resuming after suspending on a wait statement is likewise a
  // flush point; the pending unique-if violation is dropped.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic ready;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    ready = 1'b0;\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "    wait (ready);\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    ready = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, PriorityIfNoMatchDeferredWarning) {
  // §12.4.2.1: deferred violation reporting applies to priority-if as well as
  // unique/unique0. A priority-if with no matching condition and no else queues
  // a violation that is reported when the Observed region matures it.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    x = 8'd0;\n"
      "    priority if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, WaitAlreadyTrueDoesNotFlushPendingViolation) {
  // §12.4.2.1: a flush point is reached only when the procedure actually
  // suspended on the wait. A wait whose condition is already true does not
  // suspend, so a previously queued violation is not flushed and still matures.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "    wait (1'b1);\n"
      "    x = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, MaturedViolationSurvivesLaterEventControlResume) {
  // §12.4.2.1: once a pending report matures in the Observed region it can no
  // longer be flushed. The violation is detected and matured at time 0; the
  // process only resumes from the event control at a later time step, so the
  // flush on resume finds an empty queue and the already-reported violation
  // stands.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "    @e;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

}  // namespace
