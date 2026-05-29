#include <cstdint>
#include <random>

#include "fixture_simulator.h"
#include "simulator/class_object.h"
#include "simulator/process.h"

using namespace delta;

namespace {

// §18.14.3: "calls to randomize() in one instance are independent of calls to
// randomize() in other instances." Each object draws from its own generator,
// so interleaving draws between two objects never perturbs either object's
// sequence -- each replays the stream keyed by the seed it received at
// allocation.
TEST(ObjectStability, DistinctObjectsDrawIndependentStreams) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/42);
  auto* a = arena.Create<ClassObject>();
  auto* b = arena.Create<ClassObject>();
  ctx.AllocateClassObject(a);
  ctx.AllocateClassObject(b);

  std::mt19937 ref_a(a->rng_seed);
  std::mt19937 ref_b(b->rng_seed);

  // Interleave draws from the two objects; each still matches its own
  // independent reference stream.
  EXPECT_EQ(ctx.ObjectRng(a)(), ref_a());
  EXPECT_EQ(ctx.ObjectRng(b)(), ref_b());
  EXPECT_EQ(ctx.ObjectRng(a)(), ref_a());
  EXPECT_EQ(ctx.ObjectRng(a)(), ref_a());
  EXPECT_EQ(ctx.ObjectRng(b)(), ref_b());
}

// §18.14.3: "The calls to randomize() are independent of the $random system
// call." Drawing from the context-wide $random/$urandom stream after an object
// is created leaves what that object draws unchanged.
TEST(ObjectStability, ObjectDrawsUnaffectedByDollarRandom) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/7);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  std::mt19937 ref(o->rng_seed);

  // Exercise the $random / $urandom context stream before touching the object.
  ctx.Random32();
  ctx.Urandom32();
  ctx.Random32();

  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
}

// §18.14.3: object stability makes each instance's randomization reproducible
// and independent. Two contexts built from the same seed hand their first
// object the same per-object seed, so that object replays an identical draw,
// while a different context seed yields a different one.
TEST(ObjectStability, FirstObjectReplaysUnderSameContextSeed) {
  auto first_object_draw = [](uint32_t seed) {
    SourceManager mgr;
    Arena arena;
    Scheduler scheduler(arena);
    DiagEngine diag(mgr);
    SimContext ctx(scheduler, arena, diag, seed);
    auto* o = arena.Create<ClassObject>();
    ctx.AllocateClassObject(o);
    return static_cast<uint32_t>(ctx.ObjectRng(o)());
  };
  EXPECT_EQ(first_object_draw(2024), first_object_draw(2024));
  EXPECT_NE(first_object_draw(2024), first_object_draw(2025));
}

// §18.14.3: "Objects can be seeded at any time using the srandom() method."
// After reseeding mid-stream, the object's generator replays the sequence
// keyed by the new seed regardless of draws already taken.
TEST(ObjectStability, SrandomReseedsObjectStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/99);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);

  // Consume a few values, then reseed mid-stream.
  ctx.ObjectRng(o)();
  ctx.ObjectRng(o)();
  ctx.SeedObjectRng(o, /*seed=*/12345);

  std::mt19937 ref(12345u);
  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
}

// §18.14.3: seeding an object via srandom() is deterministic -- the same seed
// always yields the same stream and distinct seeds yield distinct streams --
// and the requested seed is recorded on the instance.
TEST(ObjectStability, SrandomSeedDeterminesStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/1);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);

  ctx.SeedObjectRng(o, 555);
  auto first = static_cast<uint32_t>(ctx.ObjectRng(o)());
  ctx.SeedObjectRng(o, 555);
  auto replay = static_cast<uint32_t>(ctx.ObjectRng(o)());
  ctx.SeedObjectRng(o, 777);
  auto other = static_cast<uint32_t>(ctx.ObjectRng(o)());

  EXPECT_EQ(first, replay);
  EXPECT_NE(first, other);
  EXPECT_EQ(o->rng_seed, 777u);
}

// §18.14.3: an object's randomization is independent of the thread that uses
// it. With a thread current, draws from that thread's own stream do not disturb
// the object's per-object stream.
TEST(ObjectStability, ObjectDrawsUnaffectedByThreadDraws) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/3);
  auto* proc = arena.Create<Process>();
  proc->rng_seed = 888;
  ctx.SetCurrentProcess(proc);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  std::mt19937 ref(o->rng_seed);

  // The running thread draws from its own stream; the object is untouched.
  ctx.Random32();
  ctx.Urandom32();

  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
}

// §18.14.3 edge case: object independence is isolation, not forced divergence.
// Two distinct instances seeded with the same value via srandom() each replay
// the identical stream, confirming the seed alone determines an instance's
// randomization while the instances remain separate sources.
TEST(ObjectStability, SameSrandomSeedYieldsIdenticalStreamsAcrossObjects) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/42);
  auto* a = arena.Create<ClassObject>();
  auto* b = arena.Create<ClassObject>();
  ctx.AllocateClassObject(a);
  ctx.AllocateClassObject(b);

  ctx.SeedObjectRng(a, 31337);
  ctx.SeedObjectRng(b, 31337);
  EXPECT_EQ(ctx.ObjectRng(a)(), ctx.ObjectRng(b)());
  EXPECT_EQ(ctx.ObjectRng(a)(), ctx.ObjectRng(b)());
  EXPECT_EQ(ctx.ObjectRng(a)(), ctx.ObjectRng(b)());
}

// §18.14.3 edge case: a manually seeded object stays independent of the
// $random system call. After reseeding with srandom(), exercising the
// context-wide stream still leaves the object's draws keyed solely to its seed.
TEST(ObjectStability, ReseededObjectStreamStillIndependentOfDollarRandom) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/7);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);

  ctx.SeedObjectRng(o, 24680);
  std::mt19937 ref(24680u);

  // Draw from the $random / $urandom context stream after reseeding.
  ctx.Random32();
  ctx.Urandom32();

  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
}

// §18.14.3 boundary case: srandom() accepts a zero seed and remains
// deterministic, so the same boundary seed always replays the same stream.
TEST(ObjectStability, SrandomWithZeroSeedIsDeterministic) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/5);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);

  ctx.SeedObjectRng(o, 0);
  auto first = static_cast<uint32_t>(ctx.ObjectRng(o)());
  ctx.SeedObjectRng(o, 0);
  auto replay = static_cast<uint32_t>(ctx.ObjectRng(o)());

  EXPECT_EQ(o->rng_seed, 0u);
  EXPECT_EQ(first, replay);
}

}  // namespace
