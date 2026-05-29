#include <cstdint>
#include <random>

#include "fixture_simulator.h"
#include "simulator/class_object.h"
#include "simulator/process.h"

using namespace delta;

namespace {

// §18.15: seeding an object through srandom() inside its new method guarantees
// the object's RNG already carries the chosen seed before any class member is
// randomized. Model new(): the object is allocated (taking the hierarchical
// seed from the creating thread), then the constructor reseeds it before any
// member draw. The first value a later randomize() pulls must come from the
// manually chosen stream -- the hierarchical allocation seed never governs a
// member draw.
TEST(ManuallySeedingRandomize, NewMethodSrandomInstallsSeedBeforeMemberDraw) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/42);
  auto* creator = arena.Create<Process>();
  creator->rng_seed = 1234;
  ctx.SetCurrentProcess(creator);

  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  // The hierarchical seed the object received at allocation; this is the stream
  // member randomization would have used had new() not reseeded it.
  uint32_t hierarchical_seed = o->rng_seed;

  // Inside new(), before any member is randomized, the object self-seeds.
  constexpr uint32_t kManualSeed = 9001;
  ctx.SeedObjectRng(o, kManualSeed);

  // The seeds genuinely differ, so the two streams are distinguishable: the
  // first value off the manual stream is not the first value off the
  // hierarchical one.
  EXPECT_NE(kManualSeed, hierarchical_seed);
  EXPECT_NE(static_cast<uint32_t>(std::mt19937(kManualSeed)()),
            static_cast<uint32_t>(std::mt19937(hierarchical_seed)()));

  // The first member-randomization draw replays the manual seed's stream -- the
  // hierarchical allocation seed never governs a member draw.
  std::mt19937 manual_ref(kManualSeed);
  EXPECT_EQ(ctx.ObjectRng(o)(), manual_ref());
  EXPECT_EQ(ctx.ObjectRng(o)(), manual_ref());
  EXPECT_EQ(o->rng_seed, kManualSeed);
}

// §18.15 external seeding example, modeled on creating an object with one seed
// and then reseeding it from outside the class. An object self-seeds with 200
// inside new(), is used for a while, then is reseeded to 300 by a caller that
// holds its handle. After the external reseed, the object's draws replay the
// 300 stream from its start, regardless of values already drawn under 200.
TEST(ManuallySeedingRandomize, ExternalSrandomReseedsConstructedObject) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/7);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);

  // new(200): the constructor seeds the object with 200, then some member
  // values are randomized off that stream.
  ctx.SeedObjectRng(o, 200);
  ctx.ObjectRng(o)();
  ctx.ObjectRng(o)();

  // p.srandom(300): reseed from outside the class definition.
  ctx.SeedObjectRng(o, 300);

  std::mt19937 ref(300u);
  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
  EXPECT_EQ(o->rng_seed, 300u);
}

// §18.15: srandom() may seed an object's RNG from a class method or from code
// outside the class definition. Whichever call site issues the seed, the
// facility is the same primitive acting on the object's own RNG. Two objects
// reseeded with one seed -- one as if from inside new(), the other as if from a
// handle outside the class -- land in identical RNG states.
TEST(ManuallySeedingRandomize, InMethodAndExternalSeedingAreEquivalent) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/55);
  auto* in_method = arena.Create<ClassObject>();
  auto* external = arena.Create<ClassObject>();
  ctx.AllocateClassObject(in_method);
  ctx.AllocateClassObject(external);

  constexpr uint32_t kSeed = 31337;
  // Self-seeded inside a class method (e.g. this.srandom(kSeed) in new()).
  ctx.SeedObjectRng(in_method, kSeed);
  // Seeded from outside the class definition (e.g. p.srandom(kSeed)).
  ctx.SeedObjectRng(external, kSeed);

  EXPECT_EQ(ctx.ObjectRng(in_method)(), ctx.ObjectRng(external)());
  EXPECT_EQ(ctx.ObjectRng(in_method)(), ctx.ObjectRng(external)());
  EXPECT_EQ(in_method->rng_seed, external->rng_seed);
}

// §18.15 edge case for the new()-seeding guarantee: a constructor may seed the
// object more than once before any member is randomized. Since each srandom()
// resets the object's stream, the seed in effect at the end of new() -- the
// last one applied -- is the one a later randomize() draws from.
TEST(ManuallySeedingRandomize, MultipleSrandomCallsInNewUseLastSeed) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/17);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);

  // new() reseeds twice before any member draw; the later seed must win.
  ctx.SeedObjectRng(o, 4242);
  ctx.SeedObjectRng(o, 8888);

  std::mt19937 last_ref(8888u);
  EXPECT_EQ(ctx.ObjectRng(o)(), last_ref());
  EXPECT_EQ(ctx.ObjectRng(o)(), last_ref());
  EXPECT_EQ(o->rng_seed, 8888u);
}

// §18.15 edge case for the external example: reseeding an object from outside
// the class with the very seed it already holds still restarts its stream from
// the beginning, rather than leaving the already-advanced stream in place.
TEST(ManuallySeedingRandomize, ExternalReseedToSameSeedRestartsStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/23);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);

  ctx.SeedObjectRng(o, 500);
  std::mt19937 ref(500u);
  EXPECT_EQ(ctx.ObjectRng(o)(), ref());
  EXPECT_EQ(ctx.ObjectRng(o)(), ref());

  // An external caller reseeds with the same value; the stream returns to its
  // first value rather than continuing from where it had advanced.
  ctx.SeedObjectRng(o, 500);
  std::mt19937 restart_ref(500u);
  EXPECT_EQ(ctx.ObjectRng(o)(), restart_ref());
  EXPECT_EQ(o->rng_seed, 500u);
}

}  // namespace
