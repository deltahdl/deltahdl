#include <gtest/gtest.h>

#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "helpers_fork_urandom_programs.h"
#include "helpers_scheduler.h"
#include "helpers_seeded_run.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulator/class_object.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

uint64_t RunInitialUrandom(uint32_t seed) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, seed);
  std::string src =
      "module t;\n"
      "  int unsigned v;\n"
      "  initial begin\n"
      "    v = $urandom;\n"
      "  end\n"
      "endmodule\n";
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  auto* cu = parser.Parse();
  Elaborator elab(arena, diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  Lowerer lowerer(ctx, arena, diag);
  lowerer.Lower(design);
  scheduler.Run();
  return ctx.FindVariable("v")->value.ToUint64();
}

TEST(RandomStabilityProperties, StaticProcessReplaysUnderSameInitSeed) {
  EXPECT_EQ(RunInitialUrandom(7), RunInitialUrandom(7));
}

TEST(RandomStabilityProperties, StaticProcessTracksInitializationSeed) {
  EXPECT_NE(RunInitialUrandom(7), RunInitialUrandom(8));
}

TEST(RandomStabilityProperties, DistinctObjectsGetIndependentSeeds) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, 42);
  auto* a = arena.Create<ClassObject>();
  auto* b = arena.Create<ClassObject>();
  ctx.AllocateClassObject(a);
  ctx.AllocateClassObject(b);
  EXPECT_NE(a->rng_seed, b->rng_seed);
}

TEST(RandomStabilityProperties, StaticInitObjectSeededFromInitializationRng) {
  auto first_object_seed = [](uint32_t seed) {
    SourceManager mgr;
    Arena arena;
    Scheduler scheduler(arena);
    DiagEngine diag(mgr);
    SimContext ctx(scheduler, arena, diag, seed);
    auto* o = arena.Create<ClassObject>();
    ctx.AllocateClassObject(o);
    return o->rng_seed;
  };
  EXPECT_EQ(first_object_seed(123), first_object_seed(123));
  EXPECT_NE(first_object_seed(123), first_object_seed(124));
}

TEST(RandomStabilityProperties, ObjectSeedSequenceReplaysInSameOrder) {
  auto object_seeds = [](uint32_t seed) {
    SourceManager mgr;
    Arena arena;
    Scheduler scheduler(arena);
    DiagEngine diag(mgr);
    SimContext ctx(scheduler, arena, diag, seed);
    std::vector<uint32_t> out;
    for (int i = 0; i < 4; ++i) {
      auto* o = arena.Create<ClassObject>();
      ctx.AllocateClassObject(o);
      out.push_back(o->rng_seed);
    }
    return out;
  };
  EXPECT_EQ(object_seeds(2024), object_seeds(2024));
}

TEST(RandomStabilityProperties, ChildThreadDrawDoesNotAdvanceParentStream) {
  auto run = [](bool child_draws, uint64_t& parent_after) {
    std::string src = std::string(
        "module t;\n"
        "  int unsigned a;\n"
        "  int unsigned b;\n"
        "  initial begin\n"
        "    fork\n");
    src += child_draws ? "      a = $urandom;\n" : "      a = 0;\n";
    src += std::string(
        "    join\n"
        "    b = $urandom;\n"
        "  end\n"
        "endmodule\n");
    parent_after = RunSeededAndRead(src, {"b"})[0];
  };
  uint64_t with_child = 0, without_child = 0;
  run(true, with_child);
  run(false, without_child);
  EXPECT_EQ(with_child, without_child);
}

TEST(RandomStabilityProperties, DynamicThreadSeededFromParent) {
  auto vals1 = RunParentSeededTwoForkUrandom(1);
  auto vals2 = RunParentSeededTwoForkUrandom(2);
  EXPECT_NE(vals1[0], vals2[0]);
  EXPECT_NE(vals1[1], vals2[1]);
}

TEST(RandomStabilityProperties, SingleRootSeedDefinesForkedSubtree) {
  auto a = RunParentSeededTwoForkUrandom(12345);
  auto b = RunParentSeededTwoForkUrandom(12345);
  EXPECT_EQ(a[0], b[0]);
  EXPECT_EQ(a[1], b[1]);
}

TEST(RandomStabilityProperties, DistinctStaticProcessesGetDistinctStreams) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned a;\n"
      "  int unsigned b;\n"
      "  initial a = $urandom;\n"
      "  initial b = $urandom;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto a = f.ctx.FindVariable("a")->value.ToUint64();
  auto b = f.ctx.FindVariable("b")->value.ToUint64();
  EXPECT_NE(a, b);
}

TEST(RandomStabilityProperties, ManyForkedSiblingsGetDistinctStreams) {
  auto vals = RunFourForkedSiblingUrandom();
  auto a = vals[0];
  auto b = vals[1];
  auto c = vals[2];
  auto d = vals[3];
  EXPECT_NE(a, b);
  EXPECT_NE(a, c);
  EXPECT_NE(a, d);
  EXPECT_NE(b, c);
  EXPECT_NE(b, d);
  EXPECT_NE(c, d);
}

TEST(RandomStabilityProperties, NestedForkPreservesAncestorStream) {
  auto run = [](bool grandchild_draws, uint64_t& outer_after) {
    std::string src = std::string(
        "module t;\n"
        "  int unsigned outer;\n"
        "  initial begin\n"
        "    fork\n"
        "      begin\n"
        "        fork\n"
        "          begin\n"
        "            int unsigned g;\n");
    src += grandchild_draws ? "            g = $urandom;\n"
                            : "            g = 0;\n";
    src += std::string(
        "          end\n"
        "        join\n"
        "      end\n"
        "    join\n"
        "    outer = $urandom;\n"
        "  end\n"
        "endmodule\n");
    outer_after = RunSeededAndRead(src, {"outer"})[0];
  };
  uint64_t with_draw = 0, without_draw = 0;
  run(true, with_draw);
  run(false, without_draw);
  EXPECT_EQ(with_draw, without_draw);
}

TEST(RandomStabilityProperties, ConsecutiveObjectsFollowCreatingThreadStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, 99);
  auto* proc = arena.Create<Process>();
  proc->rng_seed = 777;
  ctx.SetCurrentProcess(proc);
  auto* o1 = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o1);
  auto* o2 = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o2);
  std::mt19937 thread_stream(777u);
  auto expected1 = static_cast<uint32_t>(thread_stream());
  auto expected2 = static_cast<uint32_t>(thread_stream());
  EXPECT_EQ(o1->rng_seed, expected1);
  EXPECT_EQ(o2->rng_seed, expected2);
  EXPECT_NE(o1->rng_seed, o2->rng_seed);
}

TEST(RandomStabilityProperties, NewObjectsRandomizeFromIndependentStreams) {
  const char* src =
      "class C;\n"
      "  rand int unsigned x;\n"
      "endclass\n"
      "module t;\n"
      "  int unsigned a;\n"
      "  int unsigned b;\n"
      "  int ok1;\n"
      "  int ok2;\n"
      "  initial begin\n"
      "    static C o1 = new;\n"
      "    static C o2 = new;\n"
      "    ok1 = o1.randomize();\n"
      "    ok2 = o2.randomize();\n"
      "    a = o1.x;\n"
      "    b = o2.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_NE(RunAndGet(src, "a"), RunAndGet(src, "b"));
}

TEST(RandomStabilityProperties, ManuallySeededObjectRngPinsRandomization) {
  auto draw = [](unsigned k) {
    std::string src =
        "class C;\n"
        "  rand int unsigned x;\n"
        "endclass\n"
        "module t;\n"
        "  int unsigned a;\n"
        "  int ok;\n"
        "  initial begin\n"
        "    static C o = new;\n"
        "    o.srandom(" +
        std::to_string(k) +
        ");\n"
        "    ok = o.randomize();\n"
        "    a = o.x;\n"
        "  end\n"
        "endmodule\n";
    return RunAndGet(src, "a");
  };
  EXPECT_EQ(draw(20240712u), draw(20240712u));
  EXPECT_NE(draw(20240712u), draw(1u));
}

}  // namespace
