#include "fixture_simulator.h"
#include "simulator/process.h"

using namespace delta;

namespace {

// §18.13.3: srandom() seeds an object's RNG with the value of the given seed.
// The RNG associated with a process is seeded via the process's srandom().
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
  // First call to process::self() registers the current process with handle 1.
  auto* proc = f.ctx.FindProcessByHandle(1);
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(proc->rng_seed, 42u);
}

// §18.13.3: srandom() accepts any expression that evaluates to an int seed.
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

// §18.13.3: srandom() seeds an *object's* RNG — each process holds its own
// seed, independent of other processes.
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

// §18.13.3: "The seed can be any integral expression." Negative values are
// well-formed integral seeds; they are stored in the process's uint32 seed
// slot as the low 32 bits of the integer.
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

// §18.13.3: Reseeding overrides the previous seed.
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
