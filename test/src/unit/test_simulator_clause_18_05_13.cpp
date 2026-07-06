#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive soft constraints (18.5.13) end to end: each source program
// declares a class with a "soft expression_or_dist" constraint, calls
// randomize() from an initial block, and copies results out to module variables
// the harness reads. The parser captures the soft relation apart from the hard
// ones and the simulator builds it into a discardable (kSoft) solver
// constraint, so the behavior observed here is that of real elaborated source,
// not a hand-built solver state. A soft constraint's behavior depends entirely
// on how it is produced — the 'soft' keyword prefixing the relation — so every
// observation is made from source syntax pushed through the full pipeline.

// 18.5.13: a soft constraint that is jointly satisfiable with the active hard
// constraints is honored just like a hard preference. The soft x == 50 sits
// inside the hard range [40, 60], so the solver produces exactly 50.
TEST(ConstraintSoft, SoftHonoredWhenCompatibleWithHard) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 40; x <= 60; }\n"
      "  constraint pref { soft x == 50; }\n"
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
  EXPECT_EQ(RunAndGet(src, "rx"), 50u);
}

// 18.5.13: with no hard constraint to conflict with, a soft preference is
// satisfiable and therefore honored. A block holding only a soft constraint
// still reaches the solver (it is not treated as empty), so x is pinned to 42.
TEST(ConstraintSoft, SoftAloneIsHonored) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint pref { soft x == 42; }\n"
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
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

// 18.5.13: when a soft constraint conflicts with the hard constraints, the
// solver discards it and finds a solution satisfying the remaining constraints,
// treating the discarded soft as if replaced by the value 1 (true). randomize()
// still succeeds and the discarded preference need not hold. Here soft x == 50
// conflicts with the hard range [10, 20], so the solver discards it and returns
// an in-range value that is not the discarded preference.
TEST(ConstraintSoft, ConflictingSoftDiscardedAndTreatedAsTrue) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 10; x <= 20; }\n"
      "  constraint pref { soft x == 50; }\n"
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
  EXPECT_GE(RunAndGet(src, "rx"), 10u);
  EXPECT_LE(RunAndGet(src, "rx"), 20u);
  EXPECT_NE(RunAndGet(src, "rx"), 50u);
}

// 18.5.13: hard constraints differ from soft ones in that the solver shall
// always satisfy them; when they cannot all hold, randomize() fails outright
// rather than relaxing any of them. The two mutually exclusive hard equalities
// x == 10 and x == 20 can never both hold, so randomize() returns 0.
TEST(ConstraintSoft, UnsatisfiableHardConstraintsFailSolve) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint bad { x == 10; x == 20; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

// 18.5.13: when two or more soft constraints cannot be satisfied
// simultaneously, one or more of them is discarded so that a solution is still
// found (which one survives is governed by the priorities of 18.5.13.1). The
// two mutually exclusive soft equalities x == 10 and x == 20 cannot both hold,
// yet — unlike the hard case above — randomize() succeeds and one of the two
// preferred values is produced.
TEST(ConstraintSoft, ConflictingSoftConstraintsResolvedByDiscarding) {
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
  uint64_t rx = RunAndGet(src, "rx");
  EXPECT_TRUE(rx == 10u || rx == 20u);
}

// 18.5.13: a discarded soft constraint has no effect on the solution
// distribution — it must neither pin the variable to its preferred value nor
// remove any value the hard constraints still allow. The hard range confines x
// to {0, 1} while the conflicting soft x == 2 is discarded. Across many
// randomizations both feasible values still occur and the discarded preference
// never does, so the discarded soft neither biases nor narrows the
// distribution. Every solve also succeeds, since the hard range is satisfiable.
TEST(ConstraintSoft, DiscardedSoftDoesNotBiasDistribution) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 1; }\n"
      "  constraint pref { soft x == 2; }\n"
      "endclass\n"
      "module t;\n"
      "  int saw0;\n"
      "  int saw1;\n"
      "  int saw2;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    saw0 = 0;\n"
      "    saw1 = 0;\n"
      "    saw2 = 0;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 100; i = i + 1) begin\n"
      "      int ok;\n"
      "      ok = o.randomize();\n"
      "      if (!ok) allok = 0;\n"
      "      if (o.x == 0) saw0 = 1;\n"
      "      if (o.x == 1) saw1 = 1;\n"
      "      if (o.x == 2) saw2 = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw0"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw1"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw2"), 0u);
}

// 18.5.13 / Syntax 18-2: the operand of 'soft' is an expression_or_dist, i.e.
// any constraint expression — not only a comparison. Here the soft preference
// is a set-membership relation ('inside', 11.4.13), which lowers through a
// different path than a comparison (a general predicate rather than a folded
// bound). When it is jointly satisfiable with the hard range it is honored, so
// across many solves x always lands inside the two-value soft set {42, 43} —
// never elsewhere in the hard range [40, 45] — and both members occur.
TEST(ConstraintSoft, SoftMembershipPreferenceHonored) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 40; x <= 45; }\n"
      "  constraint pref { soft x inside {42, 43}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inset;\n"
      "  int saw42;\n"
      "  int saw43;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    inset = 1;\n"
      "    saw42 = 0;\n"
      "    saw43 = 0;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 40; i = i + 1) begin\n"
      "      int ok;\n"
      "      ok = o.randomize();\n"
      "      if (!ok) allok = 0;\n"
      "      if (o.x == 42) saw42 = 1;\n"
      "      else if (o.x == 43) saw43 = 1;\n"
      "      else inset = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
  EXPECT_EQ(RunAndGet(src, "inset"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw42"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw43"), 1u);
}

// 18.5.13 / Syntax 18-2: an implication ('->') preceded by 'soft' is likewise a
// valid soft constraint operand. With the antecedent held true by a hard
// constraint (y == 1), the soft implication reduces to a preference for its
// consequent (x == 7); being jointly satisfiable with the hard range on x it is
// honored, so every solve drives x to 7 while y stays 1.
TEST(ConstraintSoft, SoftImplicationPreferenceHonored) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint fix { y == 1; }\n"
      "  constraint rng { x >= 5; x <= 9; }\n"
      "  constraint pref { soft (y == 1) -> (x == 7); }\n"
      "endclass\n"
      "module t;\n"
      "  int allseven;\n"
      "  int ally1;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    allseven = 1;\n"
      "    ally1 = 1;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 30; i = i + 1) begin\n"
      "      int ok;\n"
      "      ok = o.randomize();\n"
      "      if (!ok) allok = 0;\n"
      "      if (o.x != 7) allseven = 0;\n"
      "      if (o.y != 1) ally1 = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
  EXPECT_EQ(RunAndGet(src, "allseven"), 1u);
  EXPECT_EQ(RunAndGet(src, "ally1"), 1u);
}

// 18.5.13 (consuming 18.5.3): a soft preference is honored within a domain
// fixed by a hard distribution built from real 'dist' syntax. The hard dist
// confines x to {5, 8}; the soft x == 5 is compatible with that set, so it is
// honored and x resolves to 5 — the preferred, dist-legal value — rather than
// being discarded. This drives the dependency's distribution syntax through the
// full pipeline while observing this subclause's honor-when-satisfiable rule.
TEST(ConstraintSoft, SoftPreferenceHonoredOverDistConstrainedDomain) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint dst { x dist {5 := 1, 8 := 1}; }\n"
      "  constraint pref { soft x == 5; }\n"
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
  EXPECT_EQ(RunAndGet(src, "rx"), 5u);
}

// 18.5.13 / Syntax 18-2: the soft operand's expression_or_dist also admits the
// dist alternative — 'soft' applied to a distribution (18.5.3 syntax). With no
// hard constraint to conflict with, the soft distribution is satisfiable and
// therefore honored: across many solves x is always drawn from the distribution
// set {5, 8} and both weighted values occur.
TEST(ConstraintSoft, SoftDistributionHonoredWhenSatisfiable) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint pref { soft x dist {5 := 1, 8 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inset;\n"
      "  int saw5;\n"
      "  int saw8;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    inset = 1;\n"
      "    saw5 = 0;\n"
      "    saw8 = 0;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 40; i = i + 1) begin\n"
      "      int ok;\n"
      "      ok = o.randomize();\n"
      "      if (!ok) allok = 0;\n"
      "      if (o.x == 5) saw5 = 1;\n"
      "      else if (o.x == 8) saw8 = 1;\n"
      "      else inset = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
  EXPECT_EQ(RunAndGet(src, "inset"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw5"), 1u);
  EXPECT_EQ(RunAndGet(src, "saw8"), 1u);
}

// 18.5.13: a soft distribution that conflicts with the hard constraints is
// discarded like any other soft constraint, so randomization still succeeds.
// The hard x == 100 admits no value the distribution {5, 8} names, so the soft
// dist is dropped and x resolves to the hard-required 100 rather than failing
// the solve.
TEST(ConstraintSoft, SoftDistributionDiscardedWhenConflicting) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint hard { x == 100; }\n"
      "  constraint pref { soft x dist {5 := 1, 8 := 1}; }\n"
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
  EXPECT_EQ(RunAndGet(src, "rx"), 100u);
}

}  // namespace
