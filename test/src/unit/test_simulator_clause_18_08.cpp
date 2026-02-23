// §18.8: Disabling random variables with rand_mode()

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulation/constraint_solver.h"

using namespace delta;

namespace {

// =============================================================================
// §18.8: rand_mode() enable/disable
// =============================================================================
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

}  // namespace
