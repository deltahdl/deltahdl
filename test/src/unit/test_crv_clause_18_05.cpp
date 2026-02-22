// §18.5: Constraint blocks

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
// §18.5.1-18.5.2: Simple constraint blocks
// =============================================================================
TEST(Constraint, SimpleRangeConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_range";
  ConstraintExpr c;
  c.kind = ConstraintKind::kRange;
  c.var_name = "x";
  c.lo = 10;
  c.hi = 20;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_GE(val, 10);
  EXPECT_LE(val, 20);
}

TEST(Constraint, EqualityConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_eq";
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = "x";
  c.lo = 42;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 42);
}

TEST(Constraint, InequalityConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_gt";
  ConstraintExpr c;
  c.kind = ConstraintKind::kGreaterThan;
  c.var_name = "x";
  c.lo = 90;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GT(solver.GetValue("x"), 90);
}

// =============================================================================
// Constraint solver ordering
// =============================================================================
TEST(Constraint, SolverOrderingMultipleBlocks) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock b1;
  b1.name = "c1";
  ConstraintExpr c1;
  c1.kind = ConstraintKind::kGreaterEqual;
  c1.var_name = "x";
  c1.lo = 100;
  b1.constraints.push_back(c1);
  solver.AddConstraintBlock(b1);

  ConstraintBlock b2;
  b2.name = "c2";
  ConstraintExpr c2;
  c2.kind = ConstraintKind::kLessEqual;
  c2.var_name = "x";
  c2.lo = 200;
  b2.constraints.push_back(c2);
  solver.AddConstraintBlock(b2);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_GE(val, 100);
  EXPECT_LE(val, 200);
}

// =============================================================================
// §18.5: Custom constraint with callback
// =============================================================================
TEST(Constraint, CustomConstraintCallback) {
  ConstraintSolver solver(42);
  RandVariable va;
  va.name = "a";
  va.min_val = 0;
  va.max_val = 50;
  solver.AddVariable(va);

  RandVariable vb;
  vb.name = "b";
  vb.min_val = 0;
  vb.max_val = 50;
  solver.AddVariable(vb);

  ConstraintBlock block;
  block.name = "c_custom";
  ConstraintExpr c;
  c.kind = ConstraintKind::kCustom;
  c.eval_fn = [](const std::unordered_map<std::string, int64_t> &vals) {
    auto ita = vals.find("a");
    auto itb = vals.find("b");
    if (ita == vals.end() || itb == vals.end())
      return true;
    return ita->second + itb->second <= 30;
  };
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_LE(solver.GetValue("a") + solver.GetValue("b"), 30);
}

// =============================================================================
// Not-equal constraint
// =============================================================================
TEST(Constraint, NotEqualConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 10;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_neq";
  ConstraintExpr c;
  c.kind = ConstraintKind::kNotEqual;
  c.var_name = "x";
  c.lo = 5;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_NE(solver.GetValue("x"), 5);
}

// =============================================================================
// Less-than constraint
// =============================================================================
TEST(Constraint, LessThanConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_lt";
  ConstraintExpr c;
  c.kind = ConstraintKind::kLessThan;
  c.var_name = "x";
  c.lo = 10;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_LT(solver.GetValue("x"), 10);
}

} // namespace
