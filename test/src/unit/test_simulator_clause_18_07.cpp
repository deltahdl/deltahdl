#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

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

// 18.7: the constraint block following 'with' can express the same constraint
// forms a class constraint can, not just simple relational/equality tests.
// Here the inline set is a set-membership form, and the solver must confine the
// drawn value to that set.
TEST(Constraint, InlineConstraintSetMembershipForm) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintExpr inline_c;
  inline_c.kind = ConstraintKind::kSetMembership;
  inline_c.var_name = "x";
  inline_c.set_values = {10, 20, 30};

  ASSERT_TRUE(solver.SolveWith({inline_c}));
  int64_t val = solver.GetValue("x");
  EXPECT_TRUE(val == 10 || val == 20 || val == 30);
}

// 18.7: the inline 'with' constraints are applied together with the object's
// own constraints, not in place of them. When the inline constraint cannot be
// satisfied alongside the block constraint, randomization fails. Here the block
// requires x >= 100 while the inline set requires x <= 50, leaving no value.
TEST(Constraint, InlineConstraintConflictingWithBlockFails) {
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
  bc.lo = 100;
  block.constraints.push_back(bc);
  solver.AddConstraintBlock(block);

  ConstraintExpr inline_c;
  inline_c.kind = ConstraintKind::kLessEqual;
  inline_c.var_name = "x";
  inline_c.lo = 50;

  EXPECT_FALSE(solver.SolveWith({inline_c}));
}

}  // namespace
