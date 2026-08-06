#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// 18.5.13.1 drives soft-constraint priority end to end. Every test below
// declares a class with real `soft` constraints (18.5.13), calls randomize()
// from an initial block, and copies the results out to module variables the
// harness reads. Priority is entirely a property of how the constraints are
// produced — their syntactic declaration order, whether they sit in an inline
// `with` block, and where they fall in the class hierarchy — so each rule is
// observed from source pushed through the full pipeline (parse, elaborate,
// simulate), not from a hand-built solver state. The parser captures each soft
// relation, the simulator lowers it to a discardable (kSoft) solver constraint,
// and the solver resolves conflicting preferences by priority.

// 18.5.13.1: within one construct, priority follows syntactic declaration order
// — a soft constraint declared later has higher priority. The two mutually
// exclusive preferences x == 10 (earlier) and x == 20 (later) sit in the same
// block; the later, higher-priority x == 20 prevails and x == 10 is discarded.
// This is the "c1 only" branch of the conceptual model, c1 being the higher.
TEST(SoftConstraintPriority, LaterSoftInSameBlockOutranksEarlier) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint prefs { soft x == 10; soft x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 20u);
}

// 18.5.13.1: priority by declaration order spans the whole enclosing construct,
// not just one block — a soft constraint in a constraint block declared later
// in the class outranks one in an earlier block. Two separate blocks prefer
// contradictory values; the later block's x == 20 prevails over the earlier
// block's x == 10.
TEST(SoftConstraintPriority, LaterConstraintBlockOutranksEarlierBlock) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint lo { soft x == 10; }\n"
      "  constraint hi { soft x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 20u);
}

// 18.5.13.1: a soft constraint within an inline (with) constraint block has
// higher priority than the constraints of the class being randomized. The class
// prefers x == 10 and the `randomize() with` block prefers x == 20; the two
// contradict, so the inline preference wins and the class one is discarded.
TEST(SoftConstraintPriority, InlineSoftOutranksClassSoft) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint pref { soft x == 10; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize() with { soft x == 20; };\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 20u);
}

// 18.5.13.1: constraints in a derived class have higher priority than all
// constraints in its superclasses. The base prefers x == 10 and the derived
// class prefers a contradictory x == 20 for the same inherited variable;
// randomizing a derived object honors the derived preference and discards the
// inherited one. The two soft constraints have distinct names, so 18.5.2
// replacement does not apply — both are active and resolved purely by priority.
TEST(SoftConstraintPriority, DerivedClassSoftOutranksSuperclassSoft) {
  const char* src =
      "class B;\n"
      "  rand int x;\n"
      "  constraint bpref { soft x == 10; }\n"
      "endclass\n"
      "class D extends B;\n"
      "  constraint dpref { soft x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    D o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 20u);
}

// 18.5.13.1: a higher-priority soft constraint that cannot be honored does not
// block a lower-priority one that can be. The hard range [0, 30] rules out the
// higher-priority preference x == 100 (declared later), so the solver discards
// it but still honors the lower-priority, satisfiable x == 15 (declared first).
// This is the "c2 only" branch of the conceptual model.
TEST(SoftConstraintPriority, LowerPrioritySoftHonoredWhenHigherConflictsHard) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 30; }\n"
      "  constraint prefs { soft x == 15; soft x == 100; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 15u);
}

// 18.5.13.1: the final fallback of the conceptual model — when neither soft
// constraint can be honored, both are discarded and the call still succeeds
// against the hard constraints alone. The hard range [0, 5] rules out both the
// lower-priority x == 50 and the higher-priority x == 90, so neither survives;
// the solve produces an in-range value that is neither discarded preference.
TEST(SoftConstraintPriority, BothSoftDiscardedWhenNeitherCanHold) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 5; }\n"
      "  constraint prefs { soft x == 50; soft x == 90; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_GE(RunAndGet(src, "rx"), 0u);
  EXPECT_LE(RunAndGet(src, "rx"), 5u);
  EXPECT_NE(RunAndGet(src, "rx"), 50u);
  EXPECT_NE(RunAndGet(src, "rx"), 90u);
}

// 18.5.13.1: a call to randomize() that involves only soft constraints can
// never fail. Two preferences (x == 1 and x == 2) contradict each other while a
// third (y == 5) is independent; with no hard constraint to satisfy the solver
// resolves the conflict by priority rather than failing — the call succeeds,
// honoring the higher-priority x == 2 and the independent y == 5.
TEST(SoftConstraintPriority, RandomizeWithOnlySoftNeverFails) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint prefs { soft x == 1; soft x == 2; soft y == 5; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "    ry = o.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 2u);
  EXPECT_EQ(RunAndGet(src, "ry"), 5u);
}

// 18.5.13.1: when the soft constraints do not contradict one another (or the
// hard constraints), the result is the same as if every constraint were
// declared hard. The two soft preferences x == 5 and y == 7 are jointly
// satisfiable, so both are honored exactly as hard equalities would be.
TEST(SoftConstraintPriority, NonContradictingSoftAllHonored) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint prefs { soft x == 5; soft y == 7; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ry;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "    ry = o.y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 5u);
  EXPECT_EQ(RunAndGet(src, "ry"), 7u);
}

}  // namespace
