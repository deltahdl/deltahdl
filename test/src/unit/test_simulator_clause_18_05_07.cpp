// §18.5.7: Iterative constraints

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
// §18.5.7: Iterative constraints (foreach)
// =============================================================================
TEST(Constraint, ForeachConstraint) {
  ConstraintSolver solver(42);
  for (int i = 0; i < 3; ++i) {
    RandVariable v;
    v.name = "arr_" + std::to_string(i);
    v.min_val = 0;
    v.max_val = 100;
    solver.AddVariable(v);
  }

  ConstraintBlock block;
  block.name = "c_foreach";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  for (int i = 0; i < 3; ++i) {
    ConstraintExpr sub;
    sub.kind = ConstraintKind::kRange;
    sub.var_name = "arr_" + std::to_string(i);
    sub.lo = 10;
    sub.hi = 50;
    fe.sub_constraints.push_back(sub);
  }
  block.constraints.push_back(fe);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  for (int i = 0; i < 3; ++i) {
    int64_t val = solver.GetValue("arr_" + std::to_string(i));
    EXPECT_GE(val, 10);
    EXPECT_LE(val, 50);
  }
}

}  // namespace
