#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <unordered_set>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

// 18.4.2 "Randc modifier": variables declared randc are random-cyclic. Each
// randomize() call returns the next value of a random permutation of the
// variable's declared range; no value repeats within one iteration over the
// range, and once the permutation is exhausted a fresh permutation is computed
// so the iteration restarts. The permutation contains only 2-state values, an
// implementation supports randc variables of at least 8 bits, and when a set of
// constraints mixes rand and randc the randc variables are solved first. These
// tests observe the constraint solver applying that cyclic behavior at the
// simulator stage.

using namespace delta;

namespace {

RandVariable MakeRandc(const char* name, int64_t lo, int64_t hi) {
  RandVariable v;
  v.name = name;
  v.qualifier = RandQualifier::kRandc;
  v.min_val = lo;
  v.max_val = hi;
  return v;
}

// 18.4.2 (claim D): the permutation sequence shall contain only 2-state values.
// Every drawn value lands inside the declared integral range — there is no X/Z
// encoding among them — across many iterations.
TEST(RandcModifierCyclic, PermutationContainsOnlyTwoStateValues) {
  ConstraintSolver solver(9);
  solver.AddVariable(MakeRandc("x", 0, 7));  // 3-bit range

  for (int i = 0; i < 100; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    // A plain integral value within [0,7]: a 2-state value, never X or Z.
    ASSERT_GE(v, 0);
    ASSERT_LE(v, 7);
  }
}

// 18.4.2 (claim E): an implementation may cap a randc variable's size but the
// cap shall be no smaller than 8 bits. An 8-bit randc is therefore supported
// and its first iteration is a full 256-value permutation with no repeats.
TEST(RandcModifierCyclic, EightBitRandcCoversEntireRangeInOneIteration) {
  ConstraintSolver solver(3);
  solver.AddVariable(MakeRandc("x", 0, 255));  // 8-bit range

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 256; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    ASSERT_GE(v, 0);
    ASSERT_LE(v, 255);
    EXPECT_TRUE(seen.insert(v).second) << "value " << v << " repeated";
  }
  EXPECT_EQ(seen.size(), 256u);
}

// 18.4.2 (claim C): the permutation only yields values that can satisfy the
// active constraints — when the remaining permutation values cannot, the
// permutation is recomputed so the iteration continues among the admissible
// values. A randc over 0..3 constrained to be below 2 therefore only ever
// returns 0 or 1, and both occur.
TEST(RandcModifierCyclic, ConstrainedRandcYieldsOnlySatisfyingValues) {
  ConstraintSolver solver(11);
  solver.AddVariable(MakeRandc("x", 0, 3));

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr lt;
  lt.kind = ConstraintKind::kLessThan;
  lt.var_name = "x";
  lt.lo = 2;  // x < 2
  block.constraints.push_back(lt);
  solver.AddConstraintBlock(block);

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 40; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    EXPECT_LT(v, 2) << "constraint-violating value produced";
    EXPECT_GE(v, 0);
    seen.insert(v);
  }
  // The two admissible values are both reached.
  EXPECT_EQ(seen.count(0), 1u);
  EXPECT_EQ(seen.count(1), 1u);
}

// 18.4.2 (claim C, "constraints change" trigger): the permutation sequence is
// recomputed not only when no remaining value can satisfy the constraints but
// also whenever the constraints on the variable change. Draw an unconstrained
// randc over 0..3 for a few calls, then add a constraint that excludes the
// lower half of the range. Every value produced after the change respects the
// new constraint — the solver re-derives the admissible permutation from the
// changed constraint set rather than continuing to emit values from the stale,
// fuller permutation it was cycling through before.
TEST(RandcModifierCyclic, PermutationRecomputedWhenConstraintsChange) {
  ConstraintSolver solver(41);
  solver.AddVariable(MakeRandc("x", 0, 3));

  // A few draws over the full, unconstrained range first.
  for (int i = 0; i < 3; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    ASSERT_GE(v, 0);
    ASSERT_LE(v, 3);
  }

  // The constraints on x now change: x shall be at least 2.
  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr ge;
  ge.kind = ConstraintKind::kGreaterEqual;
  ge.var_name = "x";
  ge.lo = 2;  // x >= 2
  block.constraints.push_back(ge);
  solver.AddConstraintBlock(block);

  // Every subsequent value lies in the recomputed admissible set {2, 3}, and
  // both of those values are reached as the cycle continues among them.
  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 30; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    EXPECT_GE(v, 2) << "value from the stale pre-change permutation produced";
    EXPECT_LE(v, 3);
    seen.insert(v);
  }
  EXPECT_EQ(seen.count(2), 1u);
  EXPECT_EQ(seen.count(3), 1u);
}

// 18.4.2 (claim A/B edge case): a randc over a single-value range (min == max)
// has a one-element permutation. Every randomize() call returns that sole value
// and the one-element iteration restarts each time, so the value never changes.
TEST(RandcModifierCyclic, DegenerateSingleValueRangeAlwaysYieldsThatValue) {
  ConstraintSolver solver(2);
  solver.AddVariable(MakeRandc("x", 7, 7));  // only the value 7 is in range

  for (int i = 0; i < 16; ++i) {
    ASSERT_TRUE(solver.Solve());
    EXPECT_EQ(solver.GetValue("x"), 7);
  }
}

// 18.4.2 (claim A edge case): the permutation spans the variable's declared
// range, which need not start at zero. A randc declared over 5..8 cycles
// through exactly {5,6,7,8} — its first iteration is a permutation of those
// four values with no repeats and no out-of-range value.
TEST(RandcModifierCyclic, PermutationCoversNonZeroBasedRange) {
  ConstraintSolver solver(17);
  solver.AddVariable(MakeRandc("x", 5, 8));

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 4; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("x");
    ASSERT_GE(v, 5);
    ASSERT_LE(v, 8);
    EXPECT_TRUE(seen.insert(v).second) << "value " << v << " repeated";
  }
  EXPECT_EQ(seen.size(), 4u);
  EXPECT_EQ(seen.count(5), 1u);
  EXPECT_EQ(seen.count(6), 1u);
  EXPECT_EQ(seen.count(7), 1u);
  EXPECT_EQ(seen.count(8), 1u);
}

// 18.4.2 (claim C / claim F error condition): when no value of the cyclic range
// can satisfy the constraints, there is no permutation value to return and
// randomize() fails. Because the randc variable is solved first, a constraint
// that excludes its entire range makes the whole randomize() call fail rather
// than silently producing an out-of-range value. A randc over 0..3 forced above
// 5 is unsatisfiable, so the solve fails on every call.
TEST(RandcModifierCyclic, UnsatisfiableConstraintFailsRandomize) {
  ConstraintSolver solver(23);
  solver.AddVariable(MakeRandc("x", 0, 3));

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr gt;
  gt.kind = ConstraintKind::kGreaterThan;
  gt.var_name = "x";
  gt.lo = 5;  // x > 5, impossible for any value in 0..3
  block.constraints.push_back(gt);
  solver.AddConstraintBlock(block);

  for (int i = 0; i < 4; ++i) {
    EXPECT_FALSE(solver.Solve());
  }
}

// 18.4.2 (claim G): when a randc variable is declared static, its cyclic state
// is static too — a single permutation sequence is shared by every instance of
// the class, so randomize() advances that one sequence regardless of which
// instance drives it. Model two instances with two solvers that share one
// static randc state: randomizing alternately through both still produces a
// single non-repeating permutation of the range, rather than each instance
// running its own independent cycle.
TEST(RandcModifierCyclic, StaticRandcSharesOneCycleAcrossInstances) {
  auto shared = std::make_shared<std::unordered_set<int64_t>>();

  auto make_static = [&](const char* name) {
    RandVariable v = MakeRandc(name, 0, 3);
    v.is_static = true;
    v.shared_randc_state = shared;
    return v;
  };

  ConstraintSolver inst_a(31);
  ConstraintSolver inst_b(37);
  inst_a.AddVariable(make_static("x"));
  inst_b.AddVariable(make_static("x"));

  // Four randomize() calls, alternating between the two instances, span one
  // full iteration of the 4-value range with no value repeated — proof of a
  // single shared cyclic sequence.
  std::unordered_set<int64_t> seen;
  ConstraintSolver* order[] = {&inst_a, &inst_b, &inst_a, &inst_b};
  for (ConstraintSolver* s : order) {
    ASSERT_TRUE(s->Solve());
    int64_t v = s->GetValue("x");
    ASSERT_GE(v, 0);
    ASSERT_LE(v, 3);
    EXPECT_TRUE(seen.insert(v).second)
        << "value " << v << " repeated across instances of a static randc";
  }
  EXPECT_EQ(seen.size(), 4u);
}

// 18.4.2 (claim A/B, observed end to end from real source): a variable
// declared randc cycles through a random permutation of its declared range,
// returning each value once before any value repeats, and once the permutation
// is exhausted a fresh one is computed so the iteration restarts. The
// distinguishing behavior — no repeat within an iteration — is exactly what
// separates randc from rand, and it must hold across successive randomize()
// calls on the same object. Declaring `randc bit [1:0] y` (range 0..3) and
// randomizing eight times drives the real production path: the declaration's
// randc modifier flows through eval_randomize into the cyclic solver, and the
// object's persistent permutation history carries the no-repeat property from
// one randomize() call to the next. The first four draws are a full
// permutation of {0,1,2,3} with no repeat (claim A), and because the fifth
// call begins a fresh iteration the next four draws are again a complete
// permutation with no repeat (claim B). Both four-call blocks being repeat-free
// is only possible if the production wiring applies the cyclic rule across
// calls rather than drawing independently each time.
TEST(RandcModifierCyclicFromSource,
     DeclaredRandcCyclesWithoutRepeatAcrossCalls) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] y;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int v0, v1, v2, v3, v4, v5, v6, v7;\n"
      "    int ok;\n"
      "    C o = new;\n"
      "    ok = o.randomize(); v0 = o.y;\n"
      "    ok = o.randomize(); v1 = o.y;\n"
      "    ok = o.randomize(); v2 = o.y;\n"
      "    ok = o.randomize(); v3 = o.y;\n"
      "    ok = o.randomize(); v4 = o.y;\n"
      "    ok = o.randomize(); v5 = o.y;\n"
      "    ok = o.randomize(); v6 = o.y;\n"
      "    ok = o.randomize(); v7 = o.y;\n"
      "    good = ((v0 != v1) && (v0 != v2) && (v0 != v3) &&\n"
      "            (v1 != v2) && (v1 != v3) && (v2 != v3) &&\n"
      "            (v4 != v5) && (v4 != v6) && (v4 != v7) &&\n"
      "            (v5 != v6) && (v5 != v7) && (v6 != v7)) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.2 (claim F, observed end to end from real source): when a class mixes an
// ordinary rand variable with a randc variable, the random-cyclic variable is
// solved first, so the presence of the rand variable never disturbs the randc
// variable's permutation. Declaring both `randc bit [1:0] r` and a constrained
// `rand bit [7:0] a` in one class and randomizing four times drives the real
// production path: eval_randomize builds one solver holding both members, the
// solver draws the randc value ahead of the rand value each call, and the
// object's persistent history keeps the randc cycle intact from call to call.
// The four randc draws are therefore a full, repeat-free permutation of
// {0,1,2,3} even though a rand variable is solved in the same randomize() call,
// while the rand variable still lands inside its own constrained domain. If the
// randc variable were tangled into the general rand solve instead of being
// committed first, its cross-call no-repeat property would not survive.
TEST(RandcModifierCyclicFromSource, RandcCyclesUndisturbedByCoexistingRand) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] r;\n"
      "  rand bit [7:0] a;\n"
      "  constraint ca { a < 200; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int r0, r1, r2, r3;\n"
      "    int a_ok;\n"
      "    int ok;\n"
      "    C o = new;\n"
      "    a_ok = 1;\n"
      "    ok = o.randomize(); r0 = o.r; if (o.a >= 200) a_ok = 0;\n"
      "    ok = o.randomize(); r1 = o.r; if (o.a >= 200) a_ok = 0;\n"
      "    ok = o.randomize(); r2 = o.r; if (o.a >= 200) a_ok = 0;\n"
      "    ok = o.randomize(); r3 = o.r; if (o.a >= 200) a_ok = 0;\n"
      "    good = (a_ok && (r0 != r1) && (r0 != r2) && (r0 != r3) &&\n"
      "            (r1 != r2) && (r1 != r3) && (r2 != r3)) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.2 (claim C, observed end to end with a real constraint from the §18.5
// dependency): the cyclic permutation only yields values that satisfy the
// active constraints — when a value would violate them it is not produced, so
// the iteration proceeds among the admissible values only. Built from real
// source: a randc variable is narrowed by a genuine `constraint` block (the
// §18.5 construct the rule consumes) declared in the class, then randomized
// repeatedly. Declaring `randc bit [1:0] x` (range 0..3) with `x < 2` restricts
// the admissible set to {0,1}; driving randomize() through the full pipeline,
// every produced value obeys the constraint and both admissible values are
// reached as the cycle runs among them. This observes the production randomize
// path applying the randc rule to a constraint parsed and elaborated from real
// syntax, not a hand-built constraint object.
TEST(RandcModifierCyclicFromSource,
     ConstrainedRandcYieldsOnlyAdmissibleValues) {
  const char* src =
      "class C;\n"
      "  randc bit [1:0] x;\n"
      "  constraint c { x < 2; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int in_range;\n"
      "    int saw0, saw1;\n"
      "    int ok;\n"
      "    C o = new;\n"
      "    in_range = 1;\n"
      "    saw0 = 0;\n"
      "    saw1 = 0;\n"
      "    for (int i = 0; i < 6; i = i + 1) begin\n"
      "      ok = o.randomize();\n"
      "      if (o.x >= 2) in_range = 0;\n"
      "      if (o.x == 0) saw0 = 1;\n"
      "      if (o.x == 1) saw1 = 1;\n"
      "    end\n"
      "    good = (in_range && saw0 && saw1) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.2 (claim E, observed end to end from real source): an implementation may
// cap the size of a randc variable but the cap is no smaller than 8 bits, so an
// 8-bit randc is supported and cycles through its full 256-value range without
// repeating. Declaring `randc bit [7:0] x` and randomizing eight times drives
// the real production path with the 8-bit input form: the declared width sets
// the cyclic range to 0..255, and the object's persistent history keeps the
// permutation repeat-free across calls. The eight successive draws are all
// distinct and each lies inside the 8-bit range — the first stretch of a full
// 256-value permutation — confirming the 8-bit width is both accepted and
// cycled over its whole range.
TEST(RandcModifierCyclicFromSource,
     EightBitRandcIsSupportedAndCyclesOverRange) {
  const char* src =
      "class C;\n"
      "  randc bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int v0, v1, v2, v3, v4, v5, v6, v7;\n"
      "    int in_range;\n"
      "    int ok;\n"
      "    C o = new;\n"
      "    in_range = 1;\n"
      "    ok = o.randomize(); v0 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v1 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v2 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v3 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v4 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v5 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v6 = o.x; if (o.x > 255) in_range = 0;\n"
      "    ok = o.randomize(); v7 = o.x; if (o.x > 255) in_range = 0;\n"
      "    good = (in_range &&\n"
      "            (v0 != v1) && (v0 != v2) && (v0 != v3) && (v0 != v4) &&\n"
      "            (v0 != v5) && (v0 != v6) && (v0 != v7) && (v1 != v2) &&\n"
      "            (v1 != v3) && (v1 != v4) && (v1 != v5) && (v1 != v6) &&\n"
      "            (v1 != v7) && (v2 != v3) && (v2 != v4) && (v2 != v5) &&\n"
      "            (v2 != v6) && (v2 != v7) && (v3 != v4) && (v3 != v5) &&\n"
      "            (v3 != v6) && (v3 != v7) && (v4 != v5) && (v4 != v6) &&\n"
      "            (v4 != v7) && (v5 != v6) && (v5 != v7) && (v6 != v7))\n"
      "           ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.4.2 (claim G, observed end to end from real source): when a randc variable
// is declared static, its cyclic state is static as well — a single permutation
// sequence is shared by every instance of the class, so randomize() advances
// that one sequence no matter which instance drives it. Built from real source:
// a class declares `static randc bit [1:0] x`, and two instances are randomized
// in alternation. Because the cyclic state is shared per class, the four draws
// spread across the two instances form one non-repeating permutation of the
// range {0,1,2,3} rather than each instance running an independent cycle (which
// would let an early draw on one instance repeat an early draw on the other).
// Driving this through the full pipeline observes the production randomize path
// sharing the randc history across instances of the declaring class. (This
// observes only the shared cyclic state that §18.4.2 governs; the separate
// value-sharing of a static property is §8.9's concern, so each instance's own
// most recent draw is read immediately after its randomize.)
TEST(RandcModifierCyclicFromSource, StaticRandcSharesOneCycleAcrossInstances) {
  const char* src =
      "class C;\n"
      "  static randc bit [1:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int v0, v1, v2, v3;\n"
      "    int ok;\n"
      "    C a = new;\n"
      "    C b = new;\n"
      "    ok = a.randomize(); v0 = a.x;\n"
      "    ok = b.randomize(); v1 = b.x;\n"
      "    ok = a.randomize(); v2 = a.x;\n"
      "    ok = b.randomize(); v3 = b.x;\n"
      "    good = ((v0 != v1) && (v0 != v2) && (v0 != v3) &&\n"
      "            (v1 != v2) && (v1 != v3) && (v2 != v3)) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
