#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <unordered_set>
#include <vector>

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

// 18.4.2 (claim A/B): an unconstrained randc cycles through a permutation of its
// whole declared range. The first iteration — a run of as many randomize() calls
// as there are values in the range — returns each value exactly once with no
// repeat (claim A); once an iteration finishes a new one starts automatically
// (claim B). Over two full iterations of a 4-value range every value occurs
// exactly twice, and each 4-call block is itself a complete permutation with no
// repeats.
TEST(RandcModifierCyclic, NewIterationStartsAfterExhaustion) {
  ConstraintSolver solver(5);
  solver.AddVariable(MakeRandc("x", 0, 3));

  std::vector<int> counts(4, 0);
  for (int iter = 0; iter < 2; ++iter) {
    std::unordered_set<int64_t> block;
    for (int i = 0; i < 4; ++i) {
      ASSERT_TRUE(solver.Solve());
      int64_t v = solver.GetValue("x");
      ASSERT_GE(v, 0);
      ASSERT_LE(v, 3);
      EXPECT_TRUE(block.insert(v).second)
          << "value " << v << " repeated within an iteration";
      ++counts[v];
    }
    EXPECT_EQ(block.size(), 4u);
  }
  for (int v = 0; v < 4; ++v) EXPECT_EQ(counts[v], 2) << "value " << v;
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
// cap shall be no smaller than 8 bits. An 8-bit randc is therefore supported and
// its first iteration is a full 256-value permutation with no repeats.
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

// 18.4.2 (claim F): when a set of random variables mixes rand and randc, the
// randc variables are solved first. The presence of an ordinary rand variable
// does not disturb the cyclic variable's permutation: the randc value still
// cycles through its full range with no repeats per iteration.
TEST(RandcModifierCyclic, RandcSolvedFirstAlongsideRand) {
  ConstraintSolver solver(13);
  solver.AddVariable(MakeRandc("r", 0, 3));
  RandVariable a;
  a.name = "a";
  a.qualifier = RandQualifier::kRand;
  a.min_val = 0;
  a.max_val = 255;
  solver.AddVariable(a);

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 4; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t r = solver.GetValue("r");
    ASSERT_GE(r, 0);
    ASSERT_LE(r, 3);
    EXPECT_TRUE(seen.insert(r).second)
        << "randc value " << r << " repeated despite rand variable present";
  }
  EXPECT_EQ(seen.size(), 4u);
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
// range, which need not start at zero. A randc declared over 5..8 cycles through
// exactly {5,6,7,8} — its first iteration is a permutation of those four values
// with no repeats and no out-of-range value.
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

  // Four randomize() calls, alternating between the two instances, span one full
  // iteration of the 4-value range with no value repeated — proof of a single
  // shared cyclic sequence.
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

}  // namespace
