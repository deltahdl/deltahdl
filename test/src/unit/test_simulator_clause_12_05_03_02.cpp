// §12.5.3.2: Case statement violation reports and multiple processes.

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"

using namespace delta;

namespace {

// §12.5.3.2: Two independent processes each execute a unique case that
// overlaps. Each process reports its own violation independently.
TEST(SimA6053202, TwoProcessesBothOverlapReportedTwice) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x, y;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    unique case(sel)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    sel = 8'd2;\n"
      "    unique case(sel)\n"
      "      8'd2: y = 8'd30;\n"
      "      8'd2: y = 8'd40;\n"
      "    endcase\n"
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

// §12.5.3.2: One process has a unique case overlap, the other has a clean
// single match. Only one violation is reported.
TEST(SimA6053202, OneProcessViolatesOtherDoesNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    unique case(8'd1)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    unique case(8'd1)\n"
      "      8'd0: y = 8'd30;\n"
      "      8'd1: y = 8'd40;\n"
      "    endcase\n"
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

// §12.5.3.2: Pending case violations are per-process. Flushing one process's
// queue does not affect another process's queue.
TEST(SimA6053202, FlushIsPerProcess) {
  SimFixture f;

  Process proc_a;
  proc_a.kind = ProcessKind::kInitial;
  Process proc_b;
  proc_b.kind = ProcessKind::kInitial;

  // Add case violation to process A.
  f.ctx.SetCurrentProcess(&proc_a);
  f.ctx.AddPendingViolation("unique case: multiple items matched");

  // Add case violation to process B.
  f.ctx.SetCurrentProcess(&proc_b);
  f.ctx.AddPendingViolation("unique case: no matching item found");

  // Flush only process A.
  f.ctx.SetCurrentProcess(&proc_a);
  f.ctx.FlushPendingViolations();

  EXPECT_TRUE(proc_a.pending_violations.empty());
  EXPECT_EQ(proc_b.pending_violations.size(), 1u);

  // Run scheduler — only proc_b's violation should mature.
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 1u);

  f.ctx.SetCurrentProcess(nullptr);
}

// §12.5.3.2: Two processes with priority case no-match → both report.
TEST(SimA6053202, TwoProcessesNoMatchBothReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    priority case(8'd5)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    y = 8'd0;\n"
      "    priority case(8'd5)\n"
      "      8'd0: y = 8'd30;\n"
      "      8'd1: y = 8'd40;\n"
      "    endcase\n"
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
