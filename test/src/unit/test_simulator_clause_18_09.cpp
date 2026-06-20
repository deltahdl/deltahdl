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

// 18.9: every constraint is active when created, and the nonvoid form returns
// 1 (true) for an active constraint. A freshly added block therefore reports
// active before any mode change is applied.
TEST(Constraint, ConstraintModeInitiallyActive) {
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
  c.lo = 5;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  EXPECT_TRUE(solver.GetConstraintMode("c_eq"));
}

TEST(Constraint, ConstraintModeDisable_ActiveSolve) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_tight";
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = "x";
  c.lo = 42;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 42);
}

TEST(Constraint, ConstraintModeDisable_DisabledSolve) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_tight";
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = "x";
  c.lo = 42;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  solver.SetConstraintMode("c_tight", false);
  EXPECT_FALSE(solver.GetConstraintMode("c_tight"));
  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 0);
  EXPECT_LE(solver.GetValue("x"), 1000);
}

// 18.9: constraint_mode() names one constraint block in the object. Turning a
// single block OFF leaves every other block active, so a sibling constraint
// still binds the solve while the disabled one is ignored.
TEST(Constraint, ConstraintModeDisableOneLeavesOthersActive) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  // One block pins x to a single value; the other confines it to a window.
  ConstraintBlock fixed;
  fixed.name = "c_fixed";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "x";
  eq.lo = 42;
  fixed.constraints.push_back(eq);
  solver.AddConstraintBlock(fixed);

  ConstraintBlock window;
  window.name = "c_window";
  ConstraintExpr rng;
  rng.kind = ConstraintKind::kRange;
  rng.var_name = "x";
  rng.lo = 100;
  rng.hi = 200;
  window.constraints.push_back(rng);
  solver.AddConstraintBlock(window);

  // Disable only the pinning block; the window block stays active.
  solver.SetConstraintMode("c_fixed", false);
  EXPECT_FALSE(solver.GetConstraintMode("c_fixed"));
  EXPECT_TRUE(solver.GetConstraintMode("c_window"));

  ASSERT_TRUE(solver.Solve());
  // The disabled equality is ignored, but the still-active window binds x.
  EXPECT_GE(solver.GetValue("x"), 100);
  EXPECT_LE(solver.GetValue("x"), 200);
}

TEST(Constraint, ConstraintModeReEnable) {
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
  c.lo = 77;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  solver.SetConstraintMode("c_eq", false);
  ASSERT_TRUE(solver.Solve());

  solver.SetConstraintMode("c_eq", true);
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 77);
}

}  // namespace
