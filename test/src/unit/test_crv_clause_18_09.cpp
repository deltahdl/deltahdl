// §18.9: Controlling constraints with constraint_mode()

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
// §18.9: constraint_mode() enable/disable
// =============================================================================
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

} // namespace
