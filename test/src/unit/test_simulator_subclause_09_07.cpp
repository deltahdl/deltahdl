#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/process.h"

using namespace delta;

namespace {

TEST(FineGrainProcessControlSimulation, SelfReturnsHandle) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] x;\n"
                      "  initial begin\n"
                      "    process p = process::self();\n"
                      "    x = (p != null) ? 1 : 0;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

TEST(FineGrainProcessControlSimulation, StatusRunningForCurrentProcess) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] x;\n"
                      "  initial begin\n"
                      "    process p = process::self();\n"
                      "    x = (p.status() == process::RUNNING) ? 1 : 0;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
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
  EXPECT_EQ(RunAndGet("module t;\n"
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
                      "x"),
            1u);
}

TEST(FineGrainProcessControlSimulation, StatusKilledAfterKill) {
  EXPECT_EQ(RunAndGet("module t;\n"
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
                      "x"),
            1u);
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

// §9.7: status() reports WAITING for a process blocked in a blocking statement.
// A forked child parked on a delay is, from the parent's viewpoint, waiting in
// a blocking statement, so querying its status() while it is parked yields
// WAITING -- distinct from the RUNNING the parent (the process making the call)
// would report for itself. The captured result is held in `w`, which the child
// never touches, so the later delayed write does not clobber the observation.
TEST(FineGrainProcessControlSimulation, StatusWaitingForBlockedProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] w;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process p;\n"
      "    w = 0;\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        p = process::self();\n"
      "        #100 x = 1;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    w = (p.status() == process::WAITING) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"w", 1u}});
}

// §9.7: calling kill() on a process already in the FINISHED state still reaps
// its live descendant subprocesses. The child spawns a grandchild with
// join_none and then finishes immediately; killing the now-finished child must
// forcibly terminate the still-parked grandchild, so its delayed write never
// runs and x stays 0. Without the descendant reap, the grandchild would fire
// x = 99 at time 100.
TEST(FineGrainProcessControlSimulation, KillOnFinishedProcessReapsDescendants) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    process child;\n"
      "    x = 0;\n"
      "    fork\n"
      "      begin\n"
      "        child = process::self();\n"
      "        fork\n"
      "          #100 x = 99;\n"
      "        join_none\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    child.kill();\n"
      "    #200;\n"
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

  auto* proc = f.ctx.FindProcessByHandle(1);
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(proc->rng_seed, 99u);
}

// §9.7: the process class prototype exposes get_randstate() and set_randstate()
// as callable members of a process handle (their RNG semantics belong to
// §18.13.4/§18.13.5). Capturing the current process's state through the process
// method yields a non-empty string, and feeding it back through set_randstate()
// on the process handle is accepted -- proving both prototype members dispatch
// on a process, not just on a generic class handle.
TEST(FineGrainProcessControlSimulation, RandStateMethodsOnProcessHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  string s;\n"
      "  int len_ok;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    s = p.get_randstate();\n"
      "    p.set_randstate(s);\n"
      "    len_ok = (s.len() > 0) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"len_ok", 1u}});

  // get_randstate() through the process method materialized the process stream.
  auto* proc = f.ctx.FindProcessByHandle(1);
  ASSERT_NE(proc, nullptr);
  EXPECT_TRUE(proc->rng_initialized);
}

TEST(FineGrainProcessControlSimulation, SuspendNoEffectOnFinished) {
  EXPECT_EQ(RunAndGet("module t;\n"
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
                      "x"),
            1u);
}

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

TEST(FineGrainProcessControlSimulation, SuspendNoEffectOnAlreadySuspended) {
  EXPECT_EQ(RunAndGet("module t;\n"
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
                      "x"),
            1u);
}

TEST(FineGrainProcessControlSimulation, SuspendNoEffectOnKilled) {
  EXPECT_EQ(RunAndGet("module t;\n"
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
                      "x"),
            1u);
}

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

// §9.7: await(), like kill()/suspend()/resume(), is restricted to a process
// created by an initial procedure, always procedure, or fork block. A process
// obtained inside a final procedure is not one of those, so awaiting it is an
// error. (This exercises await()'s own restricted-target check, a code path
// distinct from the kill/suspend/resume forms above.)
TEST(FineGrainProcessControlSimulation, AwaitOnFinalProcessIsError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  final begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.await();\n"
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
