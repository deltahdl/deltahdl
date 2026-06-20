#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_fork_urandom_programs.h"
#include "helpers_seeded_run.h"
#include "simulator/class_object.h"
#include "simulator/process.h"

using namespace delta;

namespace {

// Elaborate, lower, and run a module whose single static initial block draws
// one $urandom value, using an initialization RNG seeded with `seed`. Returns
// the value the static process drew.
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

// "Each module instance ... has an initialization RNG. Each initialization RNG
// is seeded with the default seed." and "An initialization RNG shall be used in
// the creation of static processes." The initial block is a static process; it
// draws from a stream seeded out of the initialization RNG, so replaying the
// run from the same initialization seed reproduces the draw exactly.
TEST(RandomStabilityProperties, StaticProcessReplaysUnderSameInitSeed) {
  EXPECT_EQ(RunInitialUrandom(7), RunInitialUrandom(7));
}

// "When a static process is created, its RNG is seeded with the next value from
// the initialization RNG of the [enclosing instance]." Reseeding the
// initialization RNG reseeds that static process, so its draw shifts with the
// initialization seed.
TEST(RandomStabilityProperties, StaticProcessTracksInitializationSeed) {
  EXPECT_NE(RunInitialUrandom(7), RunInitialUrandom(8));
}

// "Each class instance (object) has an independent RNG for all randomization
// methods in the class." Two objects allocated in sequence receive different
// seeds, so they own distinct random streams.
TEST(RandomStabilityProperties, DistinctObjectsGetIndependentSeeds) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/42);
  auto* a = arena.Create<ClassObject>();
  auto* b = arena.Create<ClassObject>();
  ctx.AllocateClassObject(a);
  ctx.AllocateClassObject(b);
  EXPECT_NE(a->rng_seed, b->rng_seed);
}

// "When a class object is created by a static declaration initializer, there is
// no active thread; thus, the RNG of the created object is seeded with the next
// random value of the initialization RNG ...". With no current process the
// object seed is drawn from the initialization RNG, so the first object built
// by two identically seeded contexts gets the same seed, while a different
// initialization seed yields a different one.
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

// "When an object is created using new, its RNG is seeded with the next random
// value from the thread that creates the object." With a thread current, the
// object seed is the next draw of that thread's own stream -- keyed by the
// thread's seed (555 here), independent of the context-wide initialization RNG
// (seeded 99).
TEST(RandomStabilityProperties, NewObjectSeededFromCreatingThread) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/99);
  auto* proc = arena.Create<Process>();
  proc->rng_seed = 555;
  ctx.SetCurrentProcess(proc);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  // The thread's generator is seeded lazily from its rng_seed; its first draw
  // is exactly the seed installed in the freshly created object.
  std::mt19937 thread_stream(555u);
  EXPECT_EQ(o->rng_seed, static_cast<uint32_t>(thread_stream()));
}

// "Object stability shall be preserved when object and thread creation and
// random number generation are done in the same order as before." Allocating
// the same sequence of objects from two identically seeded contexts yields the
// identical sequence of per-object seeds.
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

// §18.14.1 thread stability: each thread owns an independent RNG, so a
// randomization draw made inside a forked child consumes no values from the
// parent's stream. The parent's post-fork draw is therefore the same whether
// or not the child drew at all.
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
  run(/*child_draws=*/true, with_child);
  run(/*child_draws=*/false, without_child);
  EXPECT_EQ(with_child, without_child);
}

// §18.14.1 hierarchical seeding: a newly created dynamic thread is seeded with
// the next random value drawn from its parent. Reseeding the parent before the
// fork changes the seed material the children inherit, so their draws shift.
TEST(RandomStabilityProperties, DynamicThreadSeededFromParent) {
  auto vals1 = RunParentSeededTwoForkUrandom(/*parent_seed=*/1);
  auto vals2 = RunParentSeededTwoForkUrandom(/*parent_seed=*/2);
  EXPECT_NE(vals1[0], vals2[0]);
  EXPECT_NE(vals1[1], vals2[1]);
}

// §18.14.1: each static process is seeded with the *next* value from the
// enclosing initialization RNG, so two initial blocks in the same instance draw
// from different streams and produce different values. Edge case for the static
// branch of the initialization-RNG rule with more than one static process.
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

// §18.14.1 thread independence, breadth edge case: a fork that spawns many
// children gives each its own stream, so all of their first draws differ
// pairwise.
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

// §18.14.1 thread independence, depth edge case: independence holds across
// nested forks. A draw made in a grandchild thread must not consume from an
// ancestor's stream, so the outer thread's later draw is the same whether or
// not the grandchild drew.
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
  run(/*grandchild_draws=*/true, with_draw);
  run(/*grandchild_draws=*/false, without_draw);
  EXPECT_EQ(with_draw, without_draw);
}

// §18.14.1: an object made with new takes the *next* value from the creating
// thread. Edge case for two objects created by the same thread: their seeds are
// the thread's successive stream values, so they are distinct and follow the
// thread's own sequence.
TEST(RandomStabilityProperties, ConsecutiveObjectsFollowCreatingThreadStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/99);
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

}  // namespace
