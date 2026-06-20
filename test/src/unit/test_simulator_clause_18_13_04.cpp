#include <cstdint>
#include <random>
#include <sstream>

#include "fixture_simulator.h"
#include "simulator/class_object.h"
#include "simulator/process.h"

using namespace delta;

namespace {

// §18.13.4: get_randstate() returns the object's current RNG state as a string.
// The state must be reported as a (non-empty) string value, matching the
// `function string get_randstate()` prototype.
TEST(GetRandstate, ObjectStateIsReturnedAsString) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/42);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  ctx.SeedObjectRng(o, 1234);

  std::string state = ctx.GetRandState(o);
  EXPECT_FALSE(state.empty());
}

// §18.13.4: the returned value reflects the *current internal state* of the
// RNG. Two objects whose generators sit in the same state report identical
// strings; once one generator advances, its reported state diverges.
TEST(GetRandstate, StateTracksCurrentInternalState) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/7);
  auto* a = arena.Create<ClassObject>();
  auto* b = arena.Create<ClassObject>();
  ctx.AllocateClassObject(a);
  ctx.AllocateClassObject(b);

  ctx.SeedObjectRng(a, 9001);
  ctx.SeedObjectRng(b, 9001);
  // Identical seeds, no draws taken: the two RNGs share one internal state, so
  // their reported states are equal.
  EXPECT_EQ(ctx.GetRandState(a), ctx.GetRandState(b));

  // Advance only a's stream; its state must now differ from b's untouched one.
  ctx.ObjectRng(a)();
  EXPECT_NE(ctx.GetRandState(a), ctx.GetRandState(b));
}

// §18.13.4: the state captures the full generator state, not merely the seed.
// Two objects seeded alike but advanced a different number of draws report
// different states; advanced the same number of draws, they report equal ones.
TEST(GetRandstate, StateCapturesFullStreamPosition) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/55);
  auto* a = arena.Create<ClassObject>();
  auto* b = arena.Create<ClassObject>();
  ctx.AllocateClassObject(a);
  ctx.AllocateClassObject(b);

  ctx.SeedObjectRng(a, 31337);
  ctx.SeedObjectRng(b, 31337);

  for (int i = 0; i < 3; ++i) ctx.ObjectRng(a)();
  ctx.ObjectRng(b)();
  // Different number of draws -> different stream positions -> different
  // states.
  EXPECT_NE(ctx.GetRandState(a), ctx.GetRandState(b));

  for (int i = 0; i < 2; ++i) ctx.ObjectRng(b)();
  // Both have now advanced three draws from the same seed: states match again.
  EXPECT_EQ(ctx.GetRandState(a), ctx.GetRandState(b));
}

// §18.13.4: get_randstate() retrieves -- it must not perturb the stream. The
// value drawn immediately after reading the state is exactly the value that
// would have been drawn had the state never been read.
TEST(GetRandstate, RetrievingStateDoesNotAdvanceStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/23);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  ctx.SeedObjectRng(o, 500);

  std::mt19937 reference(500u);
  // Read the state several times, then draw; the draw must still match the
  // untouched reference stream.
  ctx.GetRandState(o);
  ctx.GetRandState(o);
  EXPECT_EQ(ctx.ObjectRng(o)(), reference());
  EXPECT_EQ(ctx.ObjectRng(o)(), reference());
}

// §18.13.4: a process likewise exposes its RNG state through get_randstate().
// The reported string reflects the process generator's current state, keyed by
// its installed seed even before the process has drawn from the stream.
TEST(GetRandstate, ProcessStateReflectsSeededGenerator) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/99);
  auto* proc = arena.Create<Process>();
  proc->rng_seed = 777;

  std::string state = ctx.GetRandState(proc);
  EXPECT_FALSE(state.empty());

  std::ostringstream expected;
  expected << std::mt19937(777u);
  EXPECT_EQ(state, expected.str());
}

// §18.13.4 edge case: an object that was never explicitly reseeded still has a
// retrievable state. get_randstate() must materialize the stream from the seed
// installed when the object was allocated, so the reported state matches a
// generator started from that allocation seed.
TEST(GetRandstate, UnseededObjectReportsAllocationState) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/123);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  // No SeedObjectRng call: the object keeps the seed drawn at allocation.

  std::string state = ctx.GetRandState(o);
  EXPECT_FALSE(state.empty());

  std::ostringstream expected;
  expected << std::mt19937(o->rng_seed);
  EXPECT_EQ(state, expected.str());
}

// §18.13.4 edge case: retrieving the state is a pure read. Reading an unchanged
// RNG twice yields the identical representation, with no draw in between.
TEST(GetRandstate, RepeatedRetrievalIsStable) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/64);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  ctx.SeedObjectRng(o, 2024);

  std::string first = ctx.GetRandState(o);
  std::string second = ctx.GetRandState(o);
  EXPECT_EQ(first, second);
}

// §18.13.4 edge case for the process path: the reported state follows the
// generator's current position. After the process draws from its stream, a
// fresh get_randstate() differs from the state read before the draw.
TEST(GetRandstate, ProcessStateTracksAdvancingStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/88);
  auto* proc = arena.Create<Process>();
  proc->rng_seed = 4096;

  std::string before = ctx.GetRandState(proc);  // lazily seeds the stream
  proc->rng();                                  // advance one draw
  std::string after = ctx.GetRandState(proc);
  EXPECT_NE(before, after);
}

}  // namespace
