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

}  // namespace
