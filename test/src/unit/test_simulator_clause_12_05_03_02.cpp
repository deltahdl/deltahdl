

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"

using namespace delta;

namespace {

TEST(CaseViolationMultiProcessSim, TwoProcessesBothOverlapReportedTwice) {
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

  EXPECT_GE(f.diag.WarningCount(), 2u);
}

TEST(CaseViolationMultiProcessSim, OneProcessViolatesOtherDoesNot) {
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

  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationMultiProcessSim, FlushIsPerProcess) {
  SimFixture f;

  Process proc_a;
  proc_a.kind = ProcessKind::kInitial;
  Process proc_b;
  proc_b.kind = ProcessKind::kInitial;

  f.ctx.SetCurrentProcess(&proc_a);
  f.ctx.AddPendingViolation("unique case: multiple items matched");

  f.ctx.SetCurrentProcess(&proc_b);
  f.ctx.AddPendingViolation("unique case: no matching item found");

  f.ctx.SetCurrentProcess(&proc_a);
  f.ctx.FlushPendingViolations();

  EXPECT_TRUE(proc_a.pending_violations.empty());
  EXPECT_EQ(proc_b.pending_violations.size(), 1u);

  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 1u);

  f.ctx.SetCurrentProcess(nullptr);
}

TEST(CaseViolationMultiProcessSim, TwoProcessesNoMatchBothReport) {
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

  EXPECT_GE(f.diag.WarningCount(), 2u);
}

TEST(CaseViolationMultiProcessSim, Unique0OverlapReportsNoMatchSilent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    unique0 case(8'd1)\n"
      "      8'd1: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    y = 8'd0;\n"
      "    unique0 case(8'd99)\n"
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
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(CaseViolationMultiProcessSim, MixedQualifiersBothViolate) {
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
      "    y = 8'd0;\n"
      "    priority case(8'd99)\n"
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
  EXPECT_GE(f.diag.WarningCount(), 2u);
}

// §12.5.3.2: case violation reports behave the same way as if violation reports
// across multiple processes (see §12.4.2.2). §12.4.2.2 demonstrates that
// behavior with a check sitting inside a subroutine called from separate
// processes. The mirror for case: a unique case inside a task whose items
// overlap on the supplied argument queues a uniqueness violation against the
// calling process, exactly as a unique if in a task would.
TEST(CaseViolationMultiProcessSim, TaskUniqueCaseOverlapReportsViolation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  task chk(input bit [7:0] s);\n"
      "    unique case(s)\n"
      "      8'd1: r = 8'd10;\n"
      "      8'd1: r = 8'd20;\n"
      "    endcase\n"
      "  endtask\n"
      "  initial chk(8'd1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §12.5.3.2 (via §12.4.2.2): when two distinct processes call the same task,
// the case violation check runs once per caller and each execution is
// independent. Both callers pass the overlapping argument, so the shared task's
// uniqueness check fails in each calling process and the violation is reported
// twice — one report per process, just as for an if.
TEST(CaseViolationMultiProcessSim, TwoProcessesCallSharedTaskCaseReportTwice) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  task chk(input bit [7:0] s);\n"
      "    unique case(s)\n"
      "      8'd1: r = 8'd10;\n"
      "      8'd1: r = 8'd20;\n"
      "    endcase\n"
      "  endtask\n"
      "  initial chk(8'd1);\n"
      "  initial chk(8'd1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_GE(f.diag.WarningCount(), 2u);
}

// §12.5.3.2 (via §12.4.2.2): the per-caller executions are independent, so a
// failure in one calling process does not implicate another. The first caller
// supplies the overlapping argument (uniqueness violation) while the second
// supplies an argument that matches exactly one item (no violation); exactly one
// report is produced.
TEST(CaseViolationMultiProcessSim, SharedTaskCaseOneCallerViolatesOtherPasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  task chk(input bit [7:0] s);\n"
      "    unique case(s)\n"
      "      8'd1: r = 8'd10;\n"
      "      8'd1: r = 8'd20;\n"
      "      8'd2: r = 8'd30;\n"
      "    endcase\n"
      "  endtask\n"
      "  initial chk(8'd1);\n"
      "  initial chk(8'd2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

// §12.5.3.2: case violation reports behave like if violation reports across
// multiple processes (see §12.4.2.2). Because each process owns its pending
// violations, a flush in one process must not disturb another process's report.
// Process A is an always_comb whose unique case transiently overlaps (a==1 and
// b==1 both match 1'b1) and queues a violation; the nonblocking update of b
// re-triggers A, whose settled single-match re-evaluation reaches a flush point
// that discards A's pending violation. Process B holds a standing unique-case
// overlap that never re-triggers. Exactly one report survives — B's — proving
// A's flush did not suppress B's report and B did not flush A's.
TEST(CaseViolationMultiProcessSim, RetriggerFlushInOneProcessSparesOther) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z, w;\n"
      "  always_comb begin\n"
      "    unique case (1'b1)\n"
      "      a: z = 8'd1;\n"
      "      b: z = 8'd2;\n"
      "      default: z = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "  initial begin\n"
      "    unique case (8'd1)\n"
      "      8'd1: w = 8'd10;\n"
      "      8'd1: w = 8'd20;\n"
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
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

}
