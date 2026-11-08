#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(UniqueIfViolationSim, MatureReportsImmediately) {
  SimFixture f;

  Process proc;
  proc.kind = ProcessKind::kInitial;
  f.ctx.SetCurrentProcess(&proc);

  proc.pending_violations.push_back(
      {SourceLoc{1, 3, 5}, "mature test", "12.4.2.1", 32, ""});
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

  f.ctx.AddPendingViolation(SourceLoc{1, 3, 5}, "violation 1",
                            Subclause("12.4.2.1"));
  f.ctx.AddPendingViolation(SourceLoc{1, 3, 5}, "violation 2",
                            Subclause("12.4.2.1"));
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

  f.ctx.AddPendingViolation(SourceLoc{1, 3, 5}, "will be flushed",
                            Subclause("12.4.2.1"));
  f.ctx.FlushPendingViolations();

  f.ctx.AddPendingViolation(SourceLoc{1, 3, 5}, "will mature",
                            Subclause("12.4.2.1"));

  f.scheduler.Run();

  EXPECT_EQ(f.diag.WarningCount(), 1u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(UniqueIfViolationSim, UniqueIfNoMatchNoElseWarning) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    x = 8'd0;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, UniqueIfNoMatchWithElseNoWarning) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, Unique0IfNoMatchNoElseNoWarning) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    x = 8'd0;\n"
      "    unique0 if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, UniqueIfOverlapWarning) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);

  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, Unique0IfOverlapWarning) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    unique0 if (1) x = 8'd10;\n"
                      "    else if (1) x = 8'd20;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);

  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, Unique0IfMatchTakesBranch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique0 if (1) x = 8'd42;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
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
  f.ctx.AddPendingViolation(SourceLoc{1, 3, 5}, "proc_a violation",
                            Subclause("12.4.2.1"));

  f.ctx.SetCurrentProcess(&proc_b);
  f.ctx.AddPendingViolation(SourceLoc{1, 3, 5}, "proc_b violation",
                            Subclause("12.4.2.1"));

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
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, AlwaysCombRetriggerFlushesPendingViolation) {
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

TEST(UniqueIfViolationSim, AlwaysLatchRetriggerFlushesPendingViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_latch begin\n"
      "    unique if (a) z = 8'd1;\n"
      "    else if (b) z = 8'd2;\n"
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

TEST(UniqueIfViolationSim, LoopIterationsEachQueueViolationAllMature) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int j = 0; j < 3; j++)\n"
      "      unique if (1) x = 8'd1;\n"
      "      else if (1) x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.diag.WarningCount(), 3u);
}

TEST(UniqueIfViolationSim, LoopViolationsAllFlushedOnReschedule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_comb begin\n"
      "    for (int j = 0; j < 2; j++)\n"
      "      unique if (a) z = 8'd1;\n"
      "      else if (b) z = 8'd2;\n"
      "      else z = 8'd0;\n"
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
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, WaitStatementFlushesPendingViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, PriorityIfNoMatchDeferredWarning) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    x = 8'd0;\n"
      "    priority if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, WaitAlreadyTrueDoesNotFlushPendingViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "    wait (1'b1);\n"
      "    x = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, MaturedViolationSurvivesLaterEventControlResume) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, OverlapReportNames12_4_2_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, z;\n"
      "  initial begin\n"
      "    a = 8'd4;\n"
      "    unique if (a == 8'd4) z = 8'd1;\n"
      "    else if (a == 8'd4) z = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "unique if: multiple conditions matched", 5,
                              "12.4.2.1"));
}

TEST(UniqueIfViolationSim, IntraAssignmentEventFlushesPendingViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  event e;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "    x = @(e) 8'd3;\n"
      "  end\n"
      "  initial #0 -> e;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, IntraAssignmentRepeatEventFlushesPendingViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  event e;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "    x = repeat (2) @(e) 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    #0 -> e;\n"
      "    #0 -> e;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, WaitForkFlushesPendingViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "    fork\n"
      "      #0 x = 8'd5;\n"
      "    join_none\n"
      "    wait fork;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, WaitOrderFlushesPendingViolation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  event a, b;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "    wait_order (a, b) x = 8'd3;\n"
      "    else x = 8'd4;\n"
      "  end\n"
      "  initial begin\n"
      "    #0 -> a;\n"
      "    #0 -> b;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, AssertControlOffStopsUniqueViolationReports) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 32);\n"
      "    unique if (0) x = 8'd1;\n"
      "    $assertcontrol(3, 32);\n"
      "    unique case (2'd3) 0: x = 8'd2; 1: x = 8'd3; endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, AssertControlKillFlushesQueuedViolationReport) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (0) x = 8'd1;\n"
      "    $assertcontrol(5, 32);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(UniqueIfViolationSim, AssertOffLeavesViolationReports) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    $assertoff;\n"
      "    unique if (0) x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(UniqueIfViolationSim, AssertControlOffForUniqueLeavesUnique0Reports) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 32);\n"
      "    unique0 if (1) x = 8'd1;\n"
      "    else if (1) x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

}  // namespace
