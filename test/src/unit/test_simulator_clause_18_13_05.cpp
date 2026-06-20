#include <cstdint>
#include <random>
#include <sstream>

#include "fixture_simulator.h"
#include "simulator/class_object.h"
#include "simulator/process.h"

using namespace delta;

namespace {

// §18.13.5: set_randstate() installs the given value as the object's RNG
// internal state. A state captured with get_randstate() and then reinstalled
// restores the generator to the exact stream position it was read from, so the
// draws taken afterwards match the draws that would have followed the capture.
TEST(SetRandstate, RestoresCapturedObjectStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/42);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  ctx.SeedObjectRng(o, 1234);

  // Capture the state, then draw a reference sequence from that position.
  std::string saved = ctx.GetRandState(o);
  uint32_t first = ctx.ObjectRng(o)();
  uint32_t second = ctx.ObjectRng(o)();

  // Reinstall the captured state: the generator must replay the same sequence.
  ctx.SetRandState(o, saved);
  EXPECT_EQ(ctx.ObjectRng(o)(), first);
  EXPECT_EQ(ctx.ObjectRng(o)(), second);
}

// §18.13.5: setting the state overwrites whatever the generator held before --
// the prior stream position is irrelevant once a new state is installed. After
// advancing an object's stream, restoring an earlier capture rewinds it.
TEST(SetRandstate, OverwritesCurrentObjectState) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/7);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  ctx.SeedObjectRng(o, 9001);

  std::string early = ctx.GetRandState(o);
  // Advance well past the captured position.
  for (int i = 0; i < 5; ++i) ctx.ObjectRng(o)();
  EXPECT_NE(ctx.GetRandState(o), early);

  // Reinstalling the early capture discards the advanced state entirely.
  ctx.SetRandState(o, early);
  EXPECT_EQ(ctx.GetRandState(o), early);
}

// §18.13.5: the state value is portable between objects -- it captures the
// generator state, not an identity. Installing one object's captured state into
// a second object makes the second draw the first's continuation.
TEST(SetRandstate, TransfersStateBetweenObjects) {
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
  ctx.SeedObjectRng(b, 424242);

  // Advance a, capture, hand the capture to b: b now mirrors a's position.
  ctx.ObjectRng(a)();
  std::string from_a = ctx.GetRandState(a);
  ctx.SetRandState(b, from_a);
  EXPECT_EQ(ctx.GetRandState(a), ctx.GetRandState(b));
  EXPECT_EQ(ctx.ObjectRng(a)(), ctx.ObjectRng(b)());
}

// §18.13.5: a process likewise has its RNG state installed via set_randstate().
// Capturing a process's state and reinstalling it after the stream advances
// rewinds the process generator to the captured position.
TEST(SetRandstate, RestoresCapturedProcessStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/99);
  auto* proc = arena.Create<Process>();
  proc->rng_seed = 777;

  std::string saved = ctx.GetRandState(proc);  // lazily seeds the stream
  uint32_t first = proc->rng();
  uint32_t second = proc->rng();

  ctx.SetRandState(proc, saved);
  EXPECT_EQ(proc->rng(), first);
  EXPECT_EQ(proc->rng(), second);
}

// §18.13.5: installing a state into a process that has never drawn (its stream
// not yet materialized) must still take effect rather than be clobbered by the
// lazy seed-on-first-use step. The reported state matches what was set.
TEST(SetRandstate, AppliesToUntouchedProcessStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/88);
  auto* proc = arena.Create<Process>();
  proc->rng_seed = 4096;

  // Build a target state from an independent generator advanced a few draws.
  std::mt19937 source(13579u);
  for (int i = 0; i < 4; ++i) source();
  std::ostringstream os;
  os << source;
  std::string target = os.str();

  ctx.SetRandState(proc, target);
  EXPECT_EQ(ctx.GetRandState(proc), target);
  // The very next draw is the source generator's continuation.
  EXPECT_EQ(proc->rng(), source());
}

// §18.13.5 edge case (object analog of the untouched-process case): installing
// a state into an object whose stream has never been materialized -- no prior
// draw, no get_randstate(), no srandom() -- must still take effect.
// SetRandState lazily seeds the allocation-default stream and then overwrites
// it, so that lazy seed must not linger and clobber the installed value.
TEST(SetRandstate, AppliesToUntouchedObjectStream) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler(arena);
  DiagEngine diag(mgr);
  SimContext ctx(scheduler, arena, diag, /*seed=*/321);
  auto* o = arena.Create<ClassObject>();
  ctx.AllocateClassObject(o);
  // No SeedObjectRng, no GetRandState, no draw: the stream is untouched.

  // Build a target state from an independent generator advanced a few draws.
  std::mt19937 source(24680u);
  for (int i = 0; i < 4; ++i) source();
  std::ostringstream os;
  os << source;
  std::string target = os.str();

  ctx.SetRandState(o, target);
  EXPECT_EQ(ctx.GetRandState(o), target);
  // The very next draw is the source generator's continuation.
  EXPECT_EQ(ctx.ObjectRng(o)(), source());
}

}  // namespace
