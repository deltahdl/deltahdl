#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §18.15 hierarchical object seeding: each object maintains its own RNG, and at
// creation that RNG is seeded from the next value of the creating thread's RNG.
// Two objects built back-to-back in the same thread therefore receive distinct
// seeds -- consecutive draws off the creating thread -- so randomizing each
// (with no manual seeding) yields different results. This drives real new()
// allocation and randomize() through the full pipeline and observes that every
// object gets its own independently seeded stream.
TEST(ManuallySeedingRandomize,
     HierarchicalObjectSeedingGivesEachObjectOwnSeed) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int diff;\n"
      "  initial begin\n"
      "    C o1 = new;\n"
      "    C o2 = new;\n"
      "    ok = o1.randomize();\n"
      "    a1 = o1.a;\n"
      "    ok = o2.randomize();\n"
      "    a2 = o2.a;\n"
      "    diff = (a1 != a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "diff"), 1u);
}

// §18.15 internal seeding example (the Packet class): a constructor seeds the
// object's RNG with this.srandom(seed). Calling srandom() in new() assures the
// object's RNG carries the chosen seed before any class member is randomized,
// so two objects constructed with the same seed produce identical randomize()
// results -- even though their hierarchical allocation seeds differ. That
// agreement shows the new()-time seed, not the allocation seed, governs the
// member draw.
TEST(ManuallySeedingRandomize, NewMethodSrandomGovernsMemberRandomization) {
  const char* src =
      "class Packet;\n"
      "  rand int header;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int h1;\n"
      "  int h2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    Packet p1 = new(200);\n"
      "    Packet p2 = new(200);\n"
      "    ok = p1.randomize();\n"
      "    h1 = p1.header;\n"
      "    ok = p2.randomize();\n"
      "    h2 = p2.header;\n"
      "    same = (h1 == h2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

// §18.15: the seed the constructor installs actually controls the member draw,
// not merely a fixed value. Two objects constructed with different seeds
// diverge
// -- the new()-time this.srandom(seed) selects the stream member randomization
// draws from.
TEST(ManuallySeedingRandomize, ConstructorSeedValueControlsResult) {
  const char* src =
      "class Packet;\n"
      "  rand int header;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int h1;\n"
      "  int h2;\n"
      "  int diff;\n"
      "  initial begin\n"
      "    Packet p1 = new(200);\n"
      "    Packet p2 = new(300);\n"
      "    ok = p1.randomize();\n"
      "    h1 = p1.header;\n"
      "    ok = p2.randomize();\n"
      "    h2 = p2.header;\n"
      "    diff = (h1 != h2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "diff"), 1u);
}

// §18.15 external seeding example (Packet p = new(200); p.srandom(300);): an
// object's RNG may be reseeded from outside the class definition through its
// handle, and this is the same facility as seeding inside new(). An object
// created with seed 200 and then externally reseeded to 300 lands in the same
// RNG state as an object constructed directly with seed 300, so their next
// randomize() results match -- external srandom() behaves identically to the
// in-method seeding.
TEST(ManuallySeedingRandomize, ExternalSrandomMatchesConstructorSeeding) {
  const char* src =
      "class Packet;\n"
      "  rand int header;\n"
      "  function new(int seed);\n"
      "    this.srandom(seed);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int h1;\n"
      "  int h2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    Packet p1 = new(200);\n"
      "    ok = p1.randomize();\n"
      "    p1.srandom(300);\n"
      "    ok = p1.randomize();\n"
      "    h1 = p1.header;\n"
      "    Packet p2 = new(300);\n"
      "    ok = p2.randomize();\n"
      "    h2 = p2.header;\n"
      "    same = (h1 == h2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

// §18.15 hierarchical object seeding, observing the source of the seed: an
// object's RNG is seeded from the RNG of the thread that creates it. Reseeding
// the creating thread (process::self().srandom) to the same value, then
// building an object, reproduces that object's implicitly drawn seed -- so two
// objects each created just after rewinding the thread's RNG randomize
// identically, with no object-level srandom in play. This drives the
// process-srandom dependency and object new()/randomize() through the full
// pipeline and shows the object seed derives from the creating thread's stream,
// not a global source.
TEST(ManuallySeedingRandomize, HierarchicalSeedDerivesFromCreatingThreadRng) {
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
      "    process pr = process::self();\n"
      "    C o1;\n"
      "    C o2;\n"
      "    pr.srandom(1000);\n"
      "    o1 = new;\n"
      "    ok = o1.randomize();\n"
      "    a1 = o1.a;\n"
      "    pr.srandom(1000);\n"
      "    o2 = new;\n"
      "    ok = o2.randomize();\n"
      "    a2 = o2.a;\n"
      "    same = (a1 == a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

// §18.15: each object's RNG is used exclusively by its own randomize(), so
// objects are randomized independently of each other. Seeding one object and
// randomizing it, then rewinding it to the same seed while a different object
// is randomized twice in between, replays the first object's identical result
// -- the other object's draws never touch this object's stream.
TEST(ManuallySeedingRandomize, PerObjectRngIsIndependentAcrossObjects) {
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
      "    C o1 = new;\n"
      "    C o2 = new;\n"
      "    o1.srandom(7);\n"
      "    ok = o1.randomize();\n"
      "    a1 = o1.a;\n"
      "    o1.srandom(7);\n"
      "    ok = o2.randomize();\n"
      "    ok = o2.randomize();\n"
      "    ok = o1.randomize();\n"
      "    a2 = o1.a;\n"
      "    same = (a1 == a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

// §18.15: an object's RNG is used exclusively by its own randomize() method, so
// its stream is independent of calls to other system randomization functions.
// After reseeding an object and randomizing it, reseeding to the same value and
// randomizing again replays the identical result -- even with intervening
// $urandom draws, which pull from the thread/context RNG and never disturb the
// object's own stream.
TEST(ManuallySeedingRandomize, ObjectRngIndependentOfOtherRandomizationFuncs) {
  const char* src =
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  int junk;\n"
      "  int a1;\n"
      "  int a2;\n"
      "  int same;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    o.srandom(77);\n"
      "    ok = o.randomize();\n"
      "    a1 = o.a;\n"
      "    o.srandom(77);\n"
      "    junk = $urandom;\n"
      "    junk = $urandom;\n"
      "    ok = o.randomize();\n"
      "    a2 = o.a;\n"
      "    same = (a1 == a2) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "same"), 1u);
}

}  // namespace
