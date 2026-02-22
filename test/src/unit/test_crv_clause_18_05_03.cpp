// §18.5.3: Distribution

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
// §18.5.3: Set membership (inside)
// =============================================================================
TEST(Constraint, InsideSetMembership) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "mode";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_inside";
  ConstraintExpr c;
  c.kind = ConstraintKind::kSetMembership;
  c.var_name = "mode";
  c.set_values = {1, 5, 10, 50};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("mode");
  EXPECT_TRUE(val == 1 || val == 5 || val == 10 || val == 50);
}

TEST(Constraint, InsideSetSingleValue) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_single";
  ConstraintExpr c;
  c.kind = ConstraintKind::kSetMembership;
  c.var_name = "x";
  c.set_values = {77};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 77);
}

} // namespace
