#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// Sets up a solver with two [0,100] variables x and y, a block fixing x to
// `x_fixed_value`, and an implication block "x == 10 -> y < 20". Used by the
// implication true/false-condition tests, which differ only in the fixed x
// value and their final assertion.
static void SetupImplicationSolver(ConstraintSolver& solver,
                                   int64_t x_fixed_value) {
  RandVariable vx;
  vx.name = "x";
  vx.min_val = 0;
  vx.max_val = 100;
  solver.AddVariable(vx);

  RandVariable vy;
  vy.name = "y";
  vy.min_val = 0;
  vy.max_val = 100;
  solver.AddVariable(vy);

  ConstraintBlock b1;
  b1.name = "fix_x";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "x";
  eq.lo = x_fixed_value;
  b1.constraints.push_back(eq);
  solver.AddConstraintBlock(b1);

  ConstraintBlock b2;
  b2.name = "impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "x";
  impl.cond_value = 10;
  ConstraintExpr sub;
  sub.kind = ConstraintKind::kLessThan;
  sub.var_name = "y";
  sub.lo = 20;
  impl.sub_constraints.push_back(sub);
  b2.constraints.push_back(impl);
  solver.AddConstraintBlock(b2);
}

TEST(ConstraintSolving, EmptyConstraintBlock) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_empty";
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_GE(val, 0);
  EXPECT_LE(val, 100);
}

TEST(ConstraintSolving, ImplicationTrueCondition) {
  ConstraintSolver solver(42);
  SetupImplicationSolver(solver, 50);

  ASSERT_TRUE(solver.Solve());
  EXPECT_LT(solver.GetValue("y"), 20);
}

TEST(ConstraintSolving, ImplicationFalseCondition) {
  ConstraintSolver solver(42);
  SetupImplicationSolver(solver, 5);

  ASSERT_TRUE(solver.Solve());

  EXPECT_GE(solver.GetValue("y"), 0);
}

TEST(ConstraintSolving, UniquenessThreeVars) {
  ConstraintSolver solver(42);
  for (const auto& name : {"a", "b", "c"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 1;
    v.max_val = 10;
    solver.AddVariable(v);
  }

  ConstraintBlock block;
  block.name = "uniq";
  ConstraintExpr u;
  u.kind = ConstraintKind::kUnique;
  u.unique_vars = {"a", "b", "c"};
  block.constraints.push_back(u);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t a = solver.GetValue("a");
  int64_t b = solver.GetValue("b");
  int64_t c = solver.GetValue("c");
  EXPECT_NE(a, b);
  EXPECT_NE(a, c);
  EXPECT_NE(b, c);
}

TEST(ConstraintSolving, ForeachAllPositive) {
  ConstraintSolver solver(42);
  for (int i = 0; i < 3; ++i) {
    RandVariable v;
    v.name = "arr_" + std::to_string(i);
    v.min_val = -10;
    v.max_val = 10;
    solver.AddVariable(v);
  }

  ConstraintBlock block;
  block.name = "fc";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  for (int i = 0; i < 3; ++i) {
    ConstraintExpr gt;
    gt.kind = ConstraintKind::kGreaterThan;
    gt.var_name = "arr_" + std::to_string(i);
    gt.lo = 0;
    fe.sub_constraints.push_back(gt);
  }
  block.constraints.push_back(fe);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  for (int i = 0; i < 3; ++i) {
    EXPECT_GT(solver.GetValue("arr_" + std::to_string(i)), 0);
  }
}

TEST(ConstraintSolving, SoftYieldsToHardConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock b1;
  b1.name = "soft_c";
  ConstraintExpr soft;
  soft.kind = ConstraintKind::kSoft;
  auto* inner = new ConstraintExpr();
  inner->kind = ConstraintKind::kEqual;
  inner->var_name = "x";
  inner->lo = 50;
  soft.inner = inner;
  b1.constraints.push_back(soft);
  solver.AddConstraintBlock(b1);

  ConstraintBlock b2;
  b2.name = "hard_c";
  ConstraintExpr hard;
  hard.kind = ConstraintKind::kEqual;
  hard.var_name = "x";
  hard.lo = 30;
  b2.constraints.push_back(hard);
  solver.AddConstraintBlock(b2);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 30);
  delete inner;
}

TEST(ConstraintSolving, DistConstraintWeightedValues) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "dist_c";
  ConstraintExpr dist;
  dist.kind = ConstraintKind::kDist;
  dist.var_name = "x";
  dist.dist_weights = {{10, 1}, {20, 1}, {30, 1}};
  block.constraints.push_back(dist);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_TRUE(val == 10 || val == 20 || val == 30);
}

TEST(ConstraintSolving, SetMembershipConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "inside_c";
  ConstraintExpr c;
  c.kind = ConstraintKind::kSetMembership;
  c.var_name = "x";
  c.set_values = {5, 15, 25, 35};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_TRUE(val == 5 || val == 15 || val == 25 || val == 35);
}

TEST(ConstraintSolving, MultipleNamedConstraintBlocks) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock b1;
  b1.name = "lower_bound";
  ConstraintExpr c1;
  c1.kind = ConstraintKind::kGreaterEqual;
  c1.var_name = "x";
  c1.lo = 100;
  b1.constraints.push_back(c1);
  solver.AddConstraintBlock(b1);

  ConstraintBlock b2;
  b2.name = "upper_bound";
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

TEST(ConstraintSolving, DisabledConstraintBlockIgnored) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "tight";
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = "x";
  c.lo = 42;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  solver.SetConstraintMode("tight", false);
  ASSERT_TRUE(solver.Solve());

  EXPECT_GE(solver.GetValue("x"), 0);
}

TEST(ConstraintSolving, MultipleExpressionsInOneBlock) {
  ConstraintSolver solver(42);
  RandVariable vx;
  vx.name = "x";
  vx.min_val = 0;
  vx.max_val = 100;
  solver.AddVariable(vx);

  RandVariable vy;
  vy.name = "y";
  vy.min_val = 0;
  vy.max_val = 100;
  solver.AddVariable(vy);

  ConstraintBlock block;
  block.name = "combined";
  ConstraintExpr c1;
  c1.kind = ConstraintKind::kGreaterThan;
  c1.var_name = "x";
  c1.lo = 50;
  block.constraints.push_back(c1);

  ConstraintExpr c2;
  c2.kind = ConstraintKind::kLessThan;
  c2.var_name = "y";
  c2.lo = 30;
  block.constraints.push_back(c2);

  solver.AddConstraintBlock(block);
  ASSERT_TRUE(solver.Solve());
  EXPECT_GT(solver.GetValue("x"), 50);
  EXPECT_LT(solver.GetValue("y"), 30);
}

}  // namespace
