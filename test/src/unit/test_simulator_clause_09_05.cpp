#include <gtest/gtest.h>

#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"

using namespace delta;

SimCoroutine MakeTestCoroutine() { co_return; }

namespace {

TEST(Process, CoroutineLifecycle) {
  SimCoroutine coro = MakeTestCoroutine();
  EXPECT_FALSE(coro.Done());

  coro.Resume();
  EXPECT_TRUE(coro.Done());
}

TEST(Process, ProcessDefaultState_Flags) {
  Process p;
  EXPECT_TRUE(p.active);
  EXPECT_FALSE(p.is_reactive);
  EXPECT_TRUE(p.Done());
}

TEST(Process, ProcessWithCoroutine) {
  auto coro = MakeTestCoroutine();
  Process p;
  p.coro = coro.Release();
  EXPECT_FALSE(p.Done());
  p.Resume();
  EXPECT_TRUE(p.Done());
}

TEST(Process, ProcessDefaultState_KindAndCoro) {
  Process p;
  EXPECT_EQ(p.kind, ProcessKind::kInitial);
  EXPECT_EQ(p.coro, nullptr);
  EXPECT_EQ(p.home_region, Region::kActive);
}

TEST(Process, ProcessDefaultState) {
  Process proc;
  EXPECT_EQ(proc.kind, ProcessKind::kInitial);
  EXPECT_EQ(proc.home_region, Region::kActive);
  EXPECT_TRUE(proc.active);
  EXPECT_FALSE(proc.is_reactive);
  EXPECT_EQ(proc.id, 0u);
}

TEST(Process, ProcessKindsEnumCoverage) {
  EXPECT_EQ(static_cast<int>(ProcessKind::kInitial), 0);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlways), 1);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlwaysComb), 2);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlwaysLatch), 3);
  EXPECT_EQ(static_cast<int>(ProcessKind::kAlwaysFF), 4);
  EXPECT_EQ(static_cast<int>(ProcessKind::kFinal), 5);
  EXPECT_EQ(static_cast<int>(ProcessKind::kContAssign), 6);
}

TEST(Process, MoveSemantics) {
  SimCoroutine a = MakeTestCoroutine();
  EXPECT_FALSE(a.Done());

  SimCoroutine* pa = &a;
  SimCoroutine b = std::move(a);
  EXPECT_FALSE(b.Done());
  EXPECT_TRUE(pa->Done());
}

TEST(Process, ProcessIdAssignment) {
  Process p1;
  p1.id = 42;
  Process p2;
  p2.id = 43;
  EXPECT_NE(p1.id, p2.id);
}

TEST(Process, CoroutineRelease) {
  SimCoroutine coro = MakeTestCoroutine();
  auto handle = coro.Release();
  EXPECT_TRUE(coro.Done());
  EXPECT_NE(handle, nullptr);

  handle.destroy();
}

TEST(Process, ProcessResumeNullSafe) {
  Process p;
  p.Resume();
  EXPECT_TRUE(p.Done());
}

TEST(Process, CoroutineDestroyOnScopeExit) {
  SimCoroutine coro = MakeTestCoroutine();
}

TEST(Process, ProcessReactiveFlag) {
  Process p;
  p.is_reactive = true;
  p.kind = ProcessKind::kInitial;
  EXPECT_TRUE(p.is_reactive);
}

TEST(Process, EachInitialRunsAsOwnThread) {
  auto val_a = RunAndGet(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd10;\n"
      "  initial b = 8'd20;\n"
      "  initial c = 8'd30;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val_a, 10u);
  auto val_b = RunAndGet(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd10;\n"
      "  initial b = 8'd20;\n"
      "  initial c = 8'd30;\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(val_b, 20u);
  auto val_c = RunAndGet(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd10;\n"
      "  initial b = 8'd20;\n"
      "  initial c = 8'd30;\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(val_c, 30u);
}

TEST(Process, EachAlwaysCombRunsAsOwnThread) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, out1, out2;\n"
      "  initial begin a = 8'd3; b = 8'd7; end\n"
      "  always_comb out1 = a + 8'd1;\n"
      "  always_comb out2 = b + 8'd2;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"out1", 4u}, {"out2", 9u}});
}

TEST(Process, MultipleContinuousAssignsEachRunAsThread) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] src, dst1, dst2;\n"
      "  initial src = 8'd5;\n"
      "  assign dst1 = src + 8'd1;\n"
      "  assign dst2 = src + 8'd2;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"dst1", 6u}, {"dst2", 7u}});
}

TEST(Process, ForkCreatesThreadPerStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd1;\n"
      "      b = 8'd2;\n"
      "      c = 8'd3;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

// §9.5: the per-parallel-statement thread rule applies to join_any groups too,
// not just join. The parent unblocks as soon as one branch finishes, but the
// remaining branches keep running as their own threads to completion.
TEST(Process, ForkJoinAnyCreatesThreadPerStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd1;\n"
      "      b = 8'd2;\n"
      "      c = 8'd3;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

// §9.5: each parallel statement in a fork-join_none group spawns its own
// dynamic process. The parent does not wait, yet every spawned thread still
// runs to completion as an independent thread of execution.
TEST(Process, ForkJoinNoneSpawnsDynamicProcessPerStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd1;\n"
      "      b = 8'd2;\n"
      "      c = 8'd3;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

// §9.5: a final procedure is its own thread of execution. It runs once at the
// end of simulation, independently of the initial thread that calls $finish.
TEST(Process, FinalRunsAsOwnThread) {
  auto marker = RunAndGet(
      "module m;\n"
      "  logic [7:0] marker;\n"
      "  initial begin marker = 8'd1; #5 $finish; end\n"
      "  final marker = 8'd42;\n"
      "endmodule\n",
      "marker");
  EXPECT_EQ(marker, 42u);
}

// §9.5: a general always procedure is its own thread. It wakes on a clock edge
// produced by a separate initial thread and drives its output.
TEST(Process, GeneralAlwaysRunsAsOwnThread) {
  auto q = RunAndGet(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  initial begin clk = 0; d = 1; #1 clk = 1; #1 $finish; end\n"
      "  always @(posedge clk) q = d;\n"
      "endmodule\n",
      "q");
  EXPECT_EQ(q, 1u);
}

// §9.5: an always_ff procedure is its own thread, waking on the clock edge
// driven by the initial thread.
TEST(Process, AlwaysFFRunsAsOwnThread) {
  auto q = RunAndGet(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  initial begin clk = 0; d = 1; #1 clk = 1; #1 $finish; end\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      "q");
  EXPECT_EQ(q, 1u);
}

// §9.5: an always_latch procedure is its own thread, sensitive to its inputs.
// Once the initial thread enables it, the latch thread follows d.
TEST(Process, AlwaysLatchRunsAsOwnThread) {
  auto q = RunAndGet(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] d, q;\n"
      "  initial begin en = 1; d = 8'hCD; end\n"
      "  always_latch if (en) q = d;\n"
      "endmodule\n",
      "q");
  EXPECT_EQ(q, 0xCDu);
}

// §9.5 edge case: a fork-join with no parallel statements creates no thread
// and does not block the spawning thread, which proceeds past the join.
TEST(Process, EmptyForkSpawnsNoThreadAndContinues) {
  auto x = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd7;\n"
      "    fork join\n"
      "    x = 8'd9;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(x, 9u);
}

// §9.5 edge case: forks nest. Each parallel statement at every nesting level
// becomes its own thread of execution.
TEST(Process, NestedForkSpawnsThreadPerStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 8'd1;\n"
      "      fork\n"
      "        b = 8'd2;\n"
      "        c = 8'd3;\n"
      "      join\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 3u}});
}

}
