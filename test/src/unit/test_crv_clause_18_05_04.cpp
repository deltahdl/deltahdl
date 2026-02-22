// §18.5.4: Uniqueness constraints

#include "simulation/constraint_solver.h"
#include <algorithm>
#include <cstdint>
#include <gtest/gtest.h>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace delta;

namespace {

// =============================================================================
// §18.5.4: Distribution constraints (dist)
// =============================================================================
TEST(Constraint, DistributionWeighted) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_dist";
  ConstraintExpr c;
  c.kind = ConstraintKind::kDist;
  c.var_name = "x";
  c.dist_weights = {{10, 1000}, {20, 1}};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  int count_10 = 0;
  for (int i = 0; i < 100; ++i) {
    ASSERT_TRUE(solver.Solve());
    if (solver.GetValue("x") == 10)
      ++count_10;
  }
  EXPECT_GT(count_10, 80);
}

TEST(Constraint, DistributionUniform) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_dist_uniform";
  ConstraintExpr c;
  c.kind = ConstraintKind::kDist;
  c.var_name = "x";
  c.dist_weights = {{1, 1}, {2, 1}, {3, 1}};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_TRUE(val >= 1 && val <= 3);
}

} // namespace
