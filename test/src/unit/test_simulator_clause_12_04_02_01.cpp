

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

TEST(UniqueIfViolationSim, Unique0IfThreeBranchOverlapWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique0 if (1) x = 8'd10;\n"
      "    else if (0) x = 8'd20;\n"
      "    else if (1) x = 8'd30;\n"
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

TEST(UniqueIfViolationSim, UniqueIfThreeBranchOverlapTakesFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    unique if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else if (1) x = 8'd30;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

}  // namespace
