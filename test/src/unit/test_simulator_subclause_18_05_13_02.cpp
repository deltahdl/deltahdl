#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// 18.5.13.2 drives 'disable soft' end to end. Each test declares a class with
// real `soft` constraints (18.5.13) and a `disable soft var;` directive, calls
// randomize() from an initial block, and copies the results out to module
// variables the harness reads. A 'disable soft' directive's effect depends
// entirely on how it is produced — the variable it names, and where the
// directive falls relative to the soft constraints in declaration order
// (18.5.13.1 priority) — so every rule is observed from source pushed through
// the full pipeline (parse, elaborate, simulate), not from a hand-built solver
// state. The parser captures the directive apart from the relations, the
// simulator lowers it to a kDisableSoft solver directive placed in declaration
// order among the block's soft constraints, and the solver discards the
// lower-priority soft constraints that reference the named variable.
//
// Because the visible effect of discarding a soft constraint is that its
// variable falls back to its unconstrained draw, the discard is observed
// statistically: randomize() is called many times and the frequency with which
// the variable takes the previously preferred value is counted. A wide band
// separates the honored case (the preference always holds) from the discarded
// case (the variable ranges freely over its hard domain).

// 18.5.13.2: a single 'disable soft' directive discards *all* the
// lower-priority soft constraints that reference the variable, not just the one
// that would otherwise prevail. Two contradictory preferences apply to x — the
// earlier soft x == 3 and the later soft x == 7 — so without the directive the
// higher-priority x == 7 governs and x is 7 on every draw. 'disable soft x' in
// a still-later block discards both: x == 7 is no longer forced (its frequency
// collapses from every draw to about a tenth) and x == 3 is likewise not
// favored, so x ends up uniform over the whole hard range. If only the nearest
// or highest-priority soft were dropped, x would still be pinned or biased.
TEST(DisableSoftConstraint, DiscardsAllLowerPrioritySoftsReferencingVariable) {
  const char* disabled =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint p1 { soft x == 3; }\n"
      "  constraint p2 { soft x == 7; }\n"
      "  constraint dis { disable soft x; }\n"
      "endclass\n"
      "module t;\n"
      "  int threes;\n"
      "  int sevens;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    threes = 0;\n"
      "    sevens = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 3) threes = threes + 1;\n"
      "      if (o.x == 7) sevens = sevens + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // Both softs discarded: x is uniform over 0..9, so each of 3 and 7 appears
  // about a tenth of the time (~60 of 600) and neither governs the draw.
  auto threes = RunAndGet(disabled, "threes");
  EXPECT_GE(threes, 15u);
  EXPECT_LE(threes, 160u);
  auto sevens = RunAndGet(disabled, "sevens");
  EXPECT_GE(sevens, 15u);
  EXPECT_LE(sevens, 160u);

  const char* control =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint p1 { soft x == 3; }\n"
      "  constraint p2 { soft x == 7; }\n"
      "endclass\n"
      "module t;\n"
      "  int sevens;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    sevens = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 7) sevens = sevens + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // Without the directive the higher-priority soft x == 7 governs every draw.
  EXPECT_EQ(RunAndGet(control, "sevens"), 600u);
}

// 18.5.13.2: a 'disable soft' constraint discards only the soft constraints
// that reference the named variable. 'disable soft x' discards the preference
// on x but leaves the independent preference on y untouched, so y == 7 is
// honored on every draw while x ranges freely. This shows the directive is
// keyed to the variable it names rather than sweeping away every soft
// constraint.
TEST(DisableSoftConstraint, DiscardsOnlySoftReferencingTheNamedVariable) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint rng { x >= 0; x <= 9; y >= 0; y <= 9; }\n"
      "  constraint px { soft x == 3; }\n"
      "  constraint py { soft y == 7; }\n"
      "  constraint dis { disable soft x; }\n"
      "endclass\n"
      "module t;\n"
      "  int xhits;\n"
      "  int yhits;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    xhits = 0;\n"
      "    yhits = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 3) xhits = xhits + 1;\n"
      "      if (o.y == 7) yhits = yhits + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // The soft on y is not referenced by 'disable soft x', so it is honored on
  // every draw; the soft on x is discarded, so x ranges freely (~60 of 600).
  EXPECT_EQ(RunAndGet(src, "yhits"), 600u);
  auto xhits = RunAndGet(src, "xhits");
  EXPECT_GE(xhits, 15u);
  EXPECT_LE(xhits, 160u);
}

// 18.5.13.2: only *lower*-priority soft constraints are discarded — a soft
// constraint declared after the directive in the same block has higher
// priority (18.5.13.1) and survives. Here 'disable soft x' discards the earlier
// block's soft x == 5, but the soft x == 8 declared after the directive in the
// same block is untouched and is honored, so x is 8 on every draw. This also
// exercises the declaration-order placement of the directive within its block:
// were it (incorrectly) treated as discarding the whole block's soft
// constraints, x would range freely instead of settling on 8.
TEST(DisableSoftConstraint, SameBlockDirectiveSparesFollowingSoft) {
  const char* src =
      "class B;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint b1 { soft x == 5; }\n"
      "  constraint b2 { disable soft x; soft x == 8; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 8u);
}

// 18.5.13.2: a 'disable soft' directive discards lower-priority soft
// constraints regardless of whether they contradict anything, extending the
// solution space beyond the values those preferences would have fixed. The
// earlier block prefers x == 5; the later block discards that preference and
// then, at higher priority, prefers x drawn from {5, 8}. With the earlier
// preference discarded x reaches 8 a substantial fraction of the time — which
// is impossible while the (non-contradicting) soft x == 5 is still in force,
// since that preference would keep x at 5. This mirrors the class B example of
// the clause.
TEST(DisableSoftConstraint, DiscardsNonContradictingSoftWideningSolutionSpace) {
  const char* src =
      "class B;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint b1 { soft x == 5; }\n"
      "  constraint b2 { disable soft x; soft x dist { 5, 8 }; }\n"
      "endclass\n"
      "module t;\n"
      "  int eights;\n"
      "  initial begin\n"
      "    B o = new;\n"
      "    eights = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 8) eights = eights + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  // The discarded soft x == 5 no longer pins x; the surviving distribution
  // splits x between 5 and 8, so x is 8 a large fraction of the time. A lenient
  // lower bound proves the preference was discarded (x could never reach 8
  // otherwise) without depending on the exact split.
  auto eights = RunAndGet(src, "eights");
  EXPECT_GE(eights, 100u);
  EXPECT_LE(eights, 500u);
}

// 18.5.13.2: a 'disable soft' directive supplied through an inline (with)
// constraint discards the class's lower-priority soft constraints — an inline
// constraint has higher priority than the class constraints (18.5.13.1), so its
// directive discards the earlier class preference. The class prefers x == 3;
// the inline 'disable soft x' discards it, so x ranges freely over the hard
// domain. The control (same randomize() with no directive) honors x == 3 on
// every draw.
TEST(DisableSoftConstraint, InlineDirectiveDiscardsClassSoft) {
  const char* disabled =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint pref { soft x == 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int hits;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    hits = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize() with { disable soft x; });\n"
      "      if (o.x == 3) hits = hits + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto hits = RunAndGet(disabled, "hits");
  EXPECT_GE(hits, 15u);
  EXPECT_LE(hits, 160u);

  const char* control =
      "class C;\n"
      "  rand int x;\n"
      "  constraint rng { x >= 0; x <= 9; }\n"
      "  constraint pref { soft x == 3; }\n"
      "endclass\n"
      "module t;\n"
      "  int hits;\n"
      "  initial begin\n"
      "    C o = new;\n"
      "    hits = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 3) hits = hits + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(control, "hits"), 600u);
}

}  // namespace
