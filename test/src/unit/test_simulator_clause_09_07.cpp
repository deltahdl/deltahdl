#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/process.h"

using namespace delta;

namespace {

TEST(FineGrainProcessControlSimulation, SelfReturnsHandle) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    x = (p != null) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

TEST(FineGrainProcessControlSimulation, StatusRunningForCurrentProcess) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    x = (p.status() == process::RUNNING) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

TEST(FineGrainProcessControlSimulation, KillTerminatesChild) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #10 x = 99;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    #20;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(FineGrainProcessControlSimulation, AwaitWaitsForTermination) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #5 a = 1;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.await();\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 1u}});
}

TEST(FineGrainProcessControlSimulation, SuspendAndResume) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #1 x = 1;\n"
      "        #1 x = 2;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.suspend();\n"
      "    #10;\n"
      "    p.resume();\n"
      "    #5;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 2u}});
}

TEST(FineGrainProcessControlSimulation, StatusFinishedAfterTermination) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    x = (p.status() == process::FINISHED) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

TEST(FineGrainProcessControlSimulation, StatusKilledAfterKill) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #100;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    x = (p.status() == process::KILLED) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

TEST(FineGrainProcessControlSimulation, KillTerminatesDescendants) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        fork\n"
      "          #10 x = 99;\n"
      "        join_none\n"
      "        #100;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    #20;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(FineGrainProcessControlSimulation, ResumeNoEffectOnNonSuspended) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #5 x = 42;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.resume();\n"
      "    #10;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

// §9.7: srandom() is a member of the process class (described in §18.13.3).
// Calling p.srandom(seed) on a process handle seeds that process's RNG.
TEST(FineGrainProcessControlSimulation, SrandomMethodOnProcessHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    p.srandom(99);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // First call to process::self() registers the current process with handle 1.
  auto* proc = f.ctx.FindProcessByHandle(1);
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(proc->rng_seed, 99u);
}

TEST(FineGrainProcessControlSimulation, SuspendNoEffectOnFinished) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.suspend();\n"
      "    x = (p.status() == process::FINISHED) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

// §9.7: "It shall be an error to call this task [await] on the current
// process, i.e., a process cannot wait for its own termination."
TEST(FineGrainProcessControlSimulation, AwaitOnCurrentProcessIsError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    p.await();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
}

// §9.7: "It shall be an error for a function to call suspend() on the
// current process, i.e., a function cannot suspend its own execution."
TEST(FineGrainProcessControlSimulation, FunctionCannotSuspendItself) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function void self_suspend();\n"
      "    process p = process::self();\n"
      "    p.suspend();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    self_suspend();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
}

// §9.7: A task is NOT a function, so calling suspend() on the current process
// from within a task is permitted (only the function restriction in §9.7
// applies to suspend-on-self).
TEST(FineGrainProcessControlSimulation, TaskCanSuspendItself) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task self_suspend_task();\n"
      "    process p = process::self();\n"
      "    p.suspend();\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        self_suspend_task();\n"
      "      end\n"
      "    join_none\n"
      "    #5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.diag.HasErrors());
}

// §9.7: "Suspending a process in the WAITING state shall cause the process
// to be desensitized to the event expression, wait condition, or delay
// expiration on which it is blocked." Observed via the suspended process
// failing to execute after its delay expires.
TEST(FineGrainProcessControlSimulation, SuspendDesensitizesWaitingProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #10 x = 99;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.suspend();\n"
      "    #20;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

// §9.7: "Suspending a process in either the SUSPENDED, FINISHED, or KILLED
// state shall have no effect." This test verifies the SUSPENDED case.
TEST(FineGrainProcessControlSimulation, SuspendNoEffectOnAlreadySuspended) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #100;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.suspend();\n"
      "    p.suspend();\n"
      "    x = (p.status() == process::SUSPENDED) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

// §9.7: "Suspending a process in either the SUSPENDED, FINISHED, or KILLED
// state shall have no effect." This test verifies the KILLED case.
TEST(FineGrainProcessControlSimulation, SuspendNoEffectOnKilled) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #100;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    p.suspend();\n"
      "    x = (p.status() == process::KILLED) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      "x"), 1u);
}

// §9.7: "The methods kill(), await(), suspend(), and resume() shall be
// restricted to a process created by an initial procedure, always procedure,
// or fork block from one of those procedures." This test exercises a final
// block, which is excluded by the restriction.
TEST(FineGrainProcessControlSimulation, KillOnFinalProcessIsError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  final begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.kill();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlSimulation, SuspendOnFinalProcessIsError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  final begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.suspend();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(FineGrainProcessControlSimulation, ResumeOnFinalProcessIsError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  final begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.resume();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
