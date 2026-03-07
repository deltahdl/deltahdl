// §12.4.2.2: If statement violation reports and multiple processes.

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"

using namespace delta;

namespace {

// §12.4.2.2: Two independent initial processes each execute a unique-if that
// overlaps. Each process has its own violation report queue, so both violations
// are reported independently.
TEST(SimA604222, TwoProcessesBothViolateReportedTwice) {
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
  // Each process independently reports an overlap violation.
  EXPECT_GE(f.diag.WarningCount(), 2u);
}

// §12.4.2.2: One process violates unique-if, another does not. Only one
// violation is reported.
TEST(SimA604222, OneProcessViolatesOtherDoesNot) {
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
  // First process: overlap. Second process: single match, no overlap.
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

// §12.4.2.2: Pending violations are per-process. Flushing one process's queue
// does not affect another process's queue.
TEST(SimA604222, FlushIsPerProcess) {
  SimFixture f;

  Process proc_a;
  proc_a.kind = ProcessKind::kInitial;
  Process proc_b;
  proc_b.kind = ProcessKind::kInitial;

  // Add violation to process A.
  f.ctx.SetCurrentProcess(&proc_a);
  f.ctx.AddPendingViolation("proc_a violation");

  // Add violation to process B.
  f.ctx.SetCurrentProcess(&proc_b);
  f.ctx.AddPendingViolation("proc_b violation");

  // Flush only process A.
  f.ctx.SetCurrentProcess(&proc_a);
  f.ctx.FlushPendingViolations();

  EXPECT_TRUE(proc_a.pending_violations.empty());
  EXPECT_EQ(proc_b.pending_violations.size(), 1u);

  // Run scheduler — only proc_b's violation should mature.
  f.scheduler.Run();
  // proc_a was flushed (Observed callback finds empty vector), proc_b matures.
  EXPECT_EQ(f.diag.WarningCount(), 1u);

  f.ctx.SetCurrentProcess(nullptr);
}

// §12.4.2.2: Two processes with unique-if no-match without else → both report.
TEST(SimA604222, TwoProcessesNoMatchBothReport) {
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
  // Each process independently reports no-match violation.
  EXPECT_GE(f.diag.WarningCount(), 2u);
}

}  // namespace
