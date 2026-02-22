// §18.7: Inline constraints—randomize() with

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
// §18.7.1: Inline constraints (randomize() with {})
// =============================================================================
TEST(Constraint, InlineConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintExpr inline_c;
  inline_c.kind = ConstraintKind::kEqual;
  inline_c.var_name = "x";
  inline_c.lo = 77;

  ASSERT_TRUE(solver.SolveWith({inline_c}));
  EXPECT_EQ(solver.GetValue("x"), 77);
}

TEST(Constraint, InlineConstraintWithBlock) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_block";
  ConstraintExpr bc;
  bc.kind = ConstraintKind::kGreaterEqual;
  bc.var_name = "x";
  bc.lo = 50;
  block.constraints.push_back(bc);
  solver.AddConstraintBlock(block);

  ConstraintExpr inline_c;
  inline_c.kind = ConstraintKind::kLessEqual;
  inline_c.var_name = "x";
  inline_c.lo = 60;

  ASSERT_TRUE(solver.SolveWith({inline_c}));
  int64_t val = solver.GetValue("x");
  EXPECT_GE(val, 50);
  EXPECT_LE(val, 60);
}

}  // namespace
