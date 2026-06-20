#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "helpers_constraint_rel.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

TEST(Constraint, RandModeDisable) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  EXPECT_TRUE(solver.GetRandMode("x"));
  solver.SetRandMode("x", false);
  EXPECT_FALSE(solver.GetRandMode("x"));

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 0);
}

TEST(Constraint, RandModeReEnable) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 1;
  v.max_val = 100;
  solver.AddVariable(v);

  solver.SetRandMode("x", false);
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 0);

  solver.SetRandMode("x", true);
  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 1);
  EXPECT_LE(solver.GetValue("x"), 100);
}

// 18.8: an inactive variable is not randomized; its value is treated as a
// state variable by the solver. Here the inactive variable's current value is
// held as a constant that another, active variable is constrained against.
TEST(Constraint, RandModeInactiveTreatedAsStateConstant) {
  ConstraintSolver solver(42);

  RandVariable x;
  x.name = "x";
  x.min_val = 0;
  x.max_val = 10;
  solver.AddVariable(x);

  RandVariable y;
  y.name = "y";
  y.min_val = 0;
  y.max_val = 10;
  solver.AddVariable(y);

  // Pin y to a known current value and make it inactive: it must keep that
  // value rather than being randomized.
  solver.SetValue("y", 5);
  solver.SetRandMode("y", false);

  AddXEqualsYPlusOneConstraint(solver);

  ASSERT_TRUE(solver.Solve());
  // y stays at its current value (state variable) and x is solved against it.
  EXPECT_EQ(solver.GetValue("y"), 5);
  EXPECT_EQ(solver.GetValue("x"), 6);
}

// 18.8: when no specific random_variable is named, the void form of
// rand_mode() applies to all random variables within the object.
TEST(Constraint, RandModeAllDisablesEveryVariable) {
  ConstraintSolver solver(42);

  RandVariable a;
  a.name = "a";
  a.min_val = 1;
  a.max_val = 100;
  solver.AddVariable(a);

  RandVariable b;
  b.name = "b";
  b.min_val = 1;
  b.max_val = 100;
  solver.AddVariable(b);

  solver.SetAllRandMode(false);
  EXPECT_FALSE(solver.GetRandMode("a"));
  EXPECT_FALSE(solver.GetRandMode("b"));

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("a"), 0);
  EXPECT_EQ(solver.GetValue("b"), 0);

  // Re-enabling all returns every variable to active randomization.
  solver.SetAllRandMode(true);
  EXPECT_TRUE(solver.GetRandMode("a"));
  EXPECT_TRUE(solver.GetRandMode("b"));

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("a"), 1);
  EXPECT_GE(solver.GetValue("b"), 1);
}

// 18.8: an inactive variable is treated the same as one that was never declared
// rand or randc. This holds for a randc variable too: once made inactive it is
// not cycled through its permutation but held at its current value as a state
// constant, exactly like an inactive rand variable.
TEST(Constraint, RandModeDisableHoldsRandcVariableAsStateConstant) {
  ConstraintSolver solver(42);

  RandVariable c;
  c.name = "c";
  c.qualifier = RandQualifier::kRandc;
  c.min_val = 0;
  c.max_val = 3;
  solver.AddVariable(c);

  solver.SetValue("c", 2);
  solver.SetRandMode("c", false);
  EXPECT_FALSE(solver.GetRandMode("c"));

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("c"), 2);
}

}  // namespace
