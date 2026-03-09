

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"

using namespace delta;

namespace {

TEST(SimA60421, DeferredOverlapViolationReported) {
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

TEST(SimA60421, DeferredPriorityNoMatchReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    priority if (0) x = 8'd10;\n"
      "    else if (0) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(SimA60421, FlushClearsPendingViolations) {
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

TEST(SimA60421, MatureReportsImmediately) {
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

TEST(SimA60421, MultipleViolationsMature) {
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

TEST(SimA60421, FlushAfterPartialAccumulation) {
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

}  // namespace
