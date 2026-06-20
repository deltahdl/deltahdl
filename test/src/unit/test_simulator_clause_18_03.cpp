#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <unordered_set>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// 18.3: for an active random variable of enum type, the solver shall select a
// value only from the set of named constants of that enum, never a value that
// lies outside the named-constant set.
TEST(EnumRandomVariable, SelectsOnlyNamedConstants) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "color";
  // Declared range spans 0..15, but only these are named enum constants.
  v.min_val = 0;
  v.max_val = 15;
  v.enum_values = {1, 4, 9};
  solver.AddVariable(v);

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 50; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t val = solver.GetValue("color");
    EXPECT_TRUE(val == 1 || val == 4 || val == 9);
    seen.insert(val);
  }
  // Over many draws the solver should exercise the whole named set.
  EXPECT_EQ(seen.size(), 3u);
}

// A randc enum variable cycles through every named constant before repeating.
TEST(EnumRandomVariable, RandcCyclesNamedConstants) {
  ConstraintSolver solver(11);
  RandVariable v;
  v.name = "state";
  v.qualifier = RandQualifier::kRandc;
  v.min_val = 0;
  v.max_val = 255;
  v.enum_values = {3, 7, 42};
  solver.AddVariable(v);

  std::unordered_set<int64_t> cycle;
  for (int i = 0; i < 3; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t val = solver.GetValue("state");
    EXPECT_TRUE(val == 3 || val == 7 || val == 42);
    cycle.insert(val);
  }
  EXPECT_EQ(cycle.size(), 3u);
}

// 18.3: the set of random values chosen shall satisfy all of the constraints.
// A solved variable observes every active constraint placed on it.
TEST(ConstraintProperties, ChosenValuesSatisfyConstraints) {
  ConstraintSolver solver(99);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr lo;
  lo.kind = ConstraintKind::kGreaterEqual;
  lo.var_name = "x";
  lo.lo = 400;
  block.constraints.push_back(lo);
  ConstraintExpr hi;
  hi.kind = ConstraintKind::kLessEqual;
  hi.var_name = "x";
  hi.lo = 410;
  block.constraints.push_back(hi);
  solver.AddConstraintBlock(block);

  for (int i = 0; i < 20; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t val = solver.GetValue("x");
    EXPECT_GE(val, 400);
    EXPECT_LE(val, 410);
  }
}

// 18.3: the solver can fail only when the problem is over-constrained, i.e.
// when no value satisfies the constraints. Contradictory equalities have no
// solution, so the solve reports failure.
TEST(ConstraintProperties, OverConstrainedProblemFails) {
  ConstraintSolver solver(1);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "contradiction";
  ConstraintExpr eq5;
  eq5.kind = ConstraintKind::kEqual;
  eq5.var_name = "x";
  eq5.lo = 5;
  block.constraints.push_back(eq5);
  ConstraintExpr eq6;
  eq6.kind = ConstraintKind::kEqual;
  eq6.var_name = "x";
  eq6.lo = 6;
  block.constraints.push_back(eq6);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
}

}  // namespace
