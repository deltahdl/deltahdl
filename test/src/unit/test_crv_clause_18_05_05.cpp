// §18.5.5: Implication

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
// §18.5.5: Unique constraints
// =============================================================================
TEST(Constraint, UniqueConstraint) {
  ConstraintSolver solver(42);
  for (int i = 0; i < 3; ++i) {
    RandVariable v;
    v.name = "u" + std::to_string(i);
    v.min_val = 0;
    v.max_val = 100;
    solver.AddVariable(v);
  }

  ConstraintBlock block;
  block.name = "c_unique";
  ConstraintExpr uc;
  uc.kind = ConstraintKind::kUnique;
  uc.unique_vars = {"u0", "u1", "u2"};
  block.constraints.push_back(uc);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t v0 = solver.GetValue("u0");
  int64_t v1 = solver.GetValue("u1");
  int64_t v2 = solver.GetValue("u2");
  EXPECT_NE(v0, v1);
  EXPECT_NE(v1, v2);
  EXPECT_NE(v0, v2);
}

}  // namespace
