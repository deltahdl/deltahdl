#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"

using namespace delta;

namespace {

TEST(SrandomSimulation, SeedsProcessRng) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    automatic process p = process::self();\n"
      "    p.srandom(42);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* proc = f.ctx.FindProcessByHandle(1);
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(proc->rng_seed, 42u);
}

TEST(SrandomSimulation, SrandomWithExpressionSeed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    automatic process p = process::self();\n"
      "    p.srandom(7 + 3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* proc = f.ctx.FindProcessByHandle(1);
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(proc->rng_seed, 10u);
}

TEST(SrandomSimulation, DistinctSeedsPerProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    process p1;\n"
      "    fork\n"
      "      begin\n"
      "        p1 = process::self();\n"
      "        p1.srandom(11);\n"
      "        #100;\n"
      "      end\n"
      "      begin\n"
      "        automatic process p2 = process::self();\n"
      "        p2.srandom(22);\n"
      "        #100;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* proc1 = f.ctx.FindProcessByHandle(1);
  auto* proc2 = f.ctx.FindProcessByHandle(2);
  ASSERT_NE(proc1, nullptr);
  ASSERT_NE(proc2, nullptr);
  EXPECT_EQ(proc1->rng_seed, 11u);
  EXPECT_EQ(proc2->rng_seed, 22u);
}

TEST(SrandomSimulation, NegativeSeed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    automatic process p = process::self();\n"
      "    p.srandom(-1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* proc = f.ctx.FindProcessByHandle(1);
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(proc->rng_seed, 0xFFFFFFFFu);
}

TEST(SrandomSimulation, RecordsMostRecentSeed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    automatic process p = process::self();\n"
      "    p.srandom(1);\n"
      "    p.srandom(2);\n"
      "    p.srandom(3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* proc = f.ctx.FindProcessByHandle(1);
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(proc->rng_seed, 3u);
}

TEST(SrandomSimulation, ProcessReseedReplaysUrandomDraw) {
  const char* src =
      "module t;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    automatic process p = process::self();\n"
      "    p.srandom(55);\n"
      "    a1 = $urandom;\n"
      "    p.srandom(55);\n"
      "    a2 = $urandom;\n"
      "    same = (a1 == a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(SrandomSimulation, ReseedingSameObjectReplaysRandomizeResult) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    o.srandom(7);\n"
      "    ok = o.randomize();\n"
      "    a1 = o.a;\n"
      "    o.srandom(7);\n"
      "    ok = o.randomize();\n"
      "    a2 = o.a;\n"
      "    same = (a1 == a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(SrandomSimulation, SeedAcceptsLocalparamConstant) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  localparam int S = 1234;\n"
      "  int ok;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static C o1 = new;\n"
      "    static C o2 = new;\n"
      "    o1.srandom(S);\n"
      "    o2.srandom(1234);\n"
      "    ok = o1.randomize();\n"
      "    ok = o2.randomize();\n"
      "    same = (o1.a == o2.a) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(SrandomSimulation, SeedAcceptsExpression) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static C o1 = new;\n"
      "    static C o2 = new;\n"
      "    o1.srandom(1000 + 234);\n"
      "    o2.srandom(1234);\n"
      "    ok = o1.randomize();\n"
      "    ok = o2.randomize();\n"
      "    same = (o1.a == o2.a) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(SrandomSimulation, SeedAcceptsParameterConstant) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t #(parameter int P = 1234);\n"
      "  int ok;\n"
      "  int same;\n"
      "  initial begin\n"
      "    static C o1 = new;\n"
      "    static C o2 = new;\n"
      "    o1.srandom(P);\n"
      "    o2.srandom(1234);\n"
      "    ok = o1.randomize();\n"
      "    ok = o2.randomize();\n"
      "    same = (o1.a == o2.a) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

TEST(SrandomSimulation, SeedAcceptsRuntimeVariable) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int same;\n"
      "  int sd;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    sd = 33;\n"
      "    o.srandom(sd);\n"
      "    ok = o.randomize();\n"
      "    a1 = o.a;\n"
      "    o.srandom(sd);\n"
      "    ok = o.randomize();\n"
      "    a2 = o.a;\n"
      "    same = (a1 == a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

}  // namespace
