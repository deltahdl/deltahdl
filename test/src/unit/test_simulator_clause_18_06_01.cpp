#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// 18.6.1: randomize() returns 1 when it successfully sets every random variable
// to a valid value. With a single active random variable and no conflicting
// constraint the solve succeeds, and the assigned value lies inside the
// variable's declared domain.
TEST(RandomizeMethod, ReturnsOneAndAssignsValidValue) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  EXPECT_TRUE(solver.Solve());
  int64_t x = solver.GetValue("x");
  EXPECT_GE(x, 0);
  EXPECT_LE(x, 100);
}

// 18.6.1: randomize() generates random values for all the active random
// variables subject to the active constraints. This mirrors the SimpleSum
// example: three random variables x, y, z with the constraint z == x + y. A
// successful solve shall leave the variables holding values that satisfy the
// constraint and stay within their declared domains.
TEST(RandomizeMethod, RandomizesInstanceSubjectToConstraint) {
  ConstraintSolver solver(11);
  RandVariable x;
  x.name = "x";
  x.min_val = 0;
  x.max_val = 7;
  solver.AddVariable(x);
  RandVariable y;
  y.name = "y";
  y.min_val = 0;
  y.max_val = 7;
  solver.AddVariable(y);
  RandVariable z;
  z.name = "z";
  z.min_val = 0;
  z.max_val = 15;
  solver.AddVariable(z);

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr sum;
  sum.kind = ConstraintKind::kCustom;
  sum.eval_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    return vals.at("z") == vals.at("x") + vals.at("y");
  };
  block.constraints.push_back(sum);
  solver.AddConstraintBlock(block);

  EXPECT_TRUE(solver.Solve());
  int64_t vx = solver.GetValue("x");
  int64_t vy = solver.GetValue("y");
  int64_t vz = solver.GetValue("z");
  EXPECT_EQ(vz, vx + vy);
  EXPECT_GE(vx, 0);
  EXPECT_LE(vx, 7);
  EXPECT_GE(vy, 0);
  EXPECT_LE(vy, 7);
  EXPECT_GE(vz, 0);
  EXPECT_LE(vz, 15);
}

// 18.6.1: otherwise randomize() returns 0. When the active constraints cannot
// all be satisfied — here a variable is pinned to two different values — the
// solve fails and reports 0 (false).
TEST(RandomizeMethod, ReturnsZeroWhenUnsatisfiable) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr eq_lo;
  eq_lo.kind = ConstraintKind::kEqual;
  eq_lo.var_name = "x";
  eq_lo.lo = 10;
  block.constraints.push_back(eq_lo);
  ConstraintExpr eq_hi;
  eq_hi.kind = ConstraintKind::kEqual;
  eq_hi.var_name = "x";
  eq_hi.lo = 20;
  block.constraints.push_back(eq_hi);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
}

// 18.6.1: randomize() generates values for ALL the active random variables in
// the object, not merely those named by a constraint. With several active
// variables and no constraints at all, a successful solve still assigns every
// one of them a value inside its own declared domain.
TEST(RandomizeMethod, AssignsEveryActiveVariable) {
  ConstraintSolver solver(3);
  RandVariable a;
  a.name = "a";
  a.min_val = 0;
  a.max_val = 5;
  solver.AddVariable(a);
  RandVariable b;
  b.name = "b";
  b.min_val = 10;
  b.max_val = 20;
  solver.AddVariable(b);
  RandVariable c;
  c.name = "c";
  c.min_val = 100;
  c.max_val = 110;
  solver.AddVariable(c);

  EXPECT_TRUE(solver.Solve());
  int64_t va = solver.GetValue("a");
  int64_t vb = solver.GetValue("b");
  int64_t vc = solver.GetValue("c");
  EXPECT_GE(va, 0);
  EXPECT_LE(va, 5);
  EXPECT_GE(vb, 10);
  EXPECT_LE(vb, 20);
  EXPECT_GE(vc, 100);
  EXPECT_LE(vc, 110);
}

}  // namespace
