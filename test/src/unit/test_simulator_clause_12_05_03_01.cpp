

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"

using namespace delta;

namespace {

TEST(CaseViolationDeferralSim, DeferredUniqueCaseOverlapReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    unique case(sel)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, DeferredPriorityCaseNoMatchReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    x = 8'd0;\n"
      "    priority case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, DeferredUniqueCaseNoMatchReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    x = 8'd0;\n"
      "    unique case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, FlushClearsPendingCaseViolations) {
  SimFixture f;

  Process proc;
  proc.kind = ProcessKind::kInitial;
  f.ctx.SetCurrentProcess(&proc);

  f.ctx.AddPendingViolation("unique case: multiple items matched");
  ASSERT_EQ(proc.pending_violations.size(), 1u);

  f.ctx.FlushPendingViolations();
  EXPECT_TRUE(proc.pending_violations.empty());

  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(CaseViolationDeferralSim, MultipleCaseViolationsMature) {
  SimFixture f;

  Process proc;
  proc.kind = ProcessKind::kInitial;
  f.ctx.SetCurrentProcess(&proc);

  f.ctx.AddPendingViolation("unique case: multiple items matched");
  f.ctx.AddPendingViolation("unique case: no matching item found");
  ASSERT_EQ(proc.pending_violations.size(), 2u);

  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 2u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(CaseViolationDeferralSim, Unique0CaseNoMatchNoDeferredViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    x = 8'd0;\n"
      "    unique0 case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseViolationDeferralSim, FlushAfterPartialAccumulation) {
  SimFixture f;

  Process proc;
  proc.kind = ProcessKind::kInitial;
  f.ctx.SetCurrentProcess(&proc);

  f.ctx.AddPendingViolation("unique case: multiple items matched");
  f.ctx.FlushPendingViolations();

  f.ctx.AddPendingViolation("unique case: no matching item found");

  f.scheduler.Run();

  EXPECT_EQ(f.diag.WarningCount(), 1u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(CaseViolationDeferralSim, Unique0CaseOverlapDeferredViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique0 case(8'd1)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, DeferredUniqueCasezOverlapReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'b00000001;\n"
      "    unique casez(sel)\n"
      "      8'b0000???1: x = 8'd10;\n"
      "      8'b000000?1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, AlwaysCombRetriggerFlushesCaseViolation) {
  // §12.5.3.1: a unique-case violation check is immune to false reports caused
  // by zero-delay glitches in the active region set, using the same mechanics
  // as the unique-if construct (§12.4.2.1). Here the always_comb first
  // evaluates with a==1 and b==1, so both case items match 1'b1 and an overlap
  // violation is queued. The nonblocking update of b re-triggers the procedure
  // within the same time step; on resume the procedure reaches a flush point
  // that discards the pending violation before the Observed region can mature
  // it. The settled state (a==1, b==0) has a single match, so nothing is
  // reported.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_comb begin\n"
      "    unique case (1'b1)\n"
      "      a: z = 8'd1;\n"
      "      b: z = 8'd2;\n"
      "      default: z = 8'd0;\n"
      "    endcase\n"
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

TEST(CaseViolationDeferralSim, DeferredPriorityCasexNoMatchReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd99;\n"
      "    x = 8'd0;\n"
      "    priority casex(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationDeferralSim, EventControlFlushesCaseViolation) {
  // §12.5.3.1: case violation reports use the same zero-delay-glitch mechanics
  // as the unique-if construct (§12.4.2.1), so a pending case violation is also
  // a flush point candidate when the procedure suspends mid-body. Here a unique
  // case queues an overlap violation, then the procedure suspends on an event
  // control and is resumed in the same time step by the other process; on
  // resume the pending violation is flushed before the Observed region matures
  // it, so nothing is reported.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique case (8'd1)\n"
      "      8'd1: x = 8'd1;\n"
      "      8'd1: x = 8'd2;\n"
      "    endcase\n"
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

TEST(CaseViolationDeferralSim, WaitStatementFlushesCaseViolation) {
  // §12.5.3.1: resuming after suspending on a wait statement is likewise a
  // flush point for a pending case violation, matching the §12.4.2.1 mechanics.
  // The queued overlap violation is dropped when the procedure resumes once the
  // wait condition becomes true within the same time step.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic ready;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    ready = 1'b0;\n"
      "    unique case (8'd1)\n"
      "      8'd1: x = 8'd1;\n"
      "      8'd1: x = 8'd2;\n"
      "    endcase\n"
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

TEST(CaseViolationDeferralSim, MaturedCaseViolationSurvivesLaterResume) {
  // §12.5.3.1 / §12.4.2.1 edge case: once a deferred case violation matures in
  // the Observed region it can no longer be flushed. The overlap is detected
  // and matured at time 0; the procedure only resumes from the event control at
  // a later time step, so the flush on resume finds an empty queue and the
  // already-reported violation stands.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique case (8'd1)\n"
      "      8'd1: x = 8'd1;\n"
      "      8'd1: x = 8'd2;\n"
      "    endcase\n"
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
