#include "fixture_simulator.h"
#include "simulator/process.h"

using namespace delta;

namespace {

TEST(SrandomSimulation, SeedsProcessRng) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
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
      "    process p = process::self();\n"
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
      "        process p2 = process::self();\n"
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
      "    process p = process::self();\n"
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
      "    process p = process::self();\n"
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

}  // namespace
