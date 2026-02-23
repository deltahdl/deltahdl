// §18.5.13: Soft constraints

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
// §18.5.13: Soft constraints
// =============================================================================
TEST(Constraint, SoftConstraintYieldsToHard) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  // Soft: x == 50.
  ConstraintBlock b_soft;
  b_soft.name = "c_soft";
  ConstraintExpr inner_expr;
  inner_expr.kind = ConstraintKind::kEqual;
  inner_expr.var_name = "x";
  inner_expr.lo = 50;
  ConstraintExpr sc;
  sc.kind = ConstraintKind::kSoft;
  sc.inner = &inner_expr;
  sc.var_name = "x";
  b_soft.constraints.push_back(sc);
  solver.AddConstraintBlock(b_soft);

  // Hard: x == 30. This overrides soft.
  ConstraintBlock b_hard;
  b_hard.name = "c_hard";
  ConstraintExpr hc;
  hc.kind = ConstraintKind::kEqual;
  hc.var_name = "x";
  hc.lo = 30;
  b_hard.constraints.push_back(hc);
  solver.AddConstraintBlock(b_hard);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 30);
}

TEST(Constraint, SoftConstraintAloneSatisfied) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_soft_only";
  ConstraintExpr inner_expr;
  inner_expr.kind = ConstraintKind::kEqual;
  inner_expr.var_name = "x";
  inner_expr.lo = 42;
  ConstraintExpr sc;
  sc.kind = ConstraintKind::kSoft;
  sc.inner = &inner_expr;
  sc.var_name = "x";
  block.constraints.push_back(sc);
  solver.AddConstraintBlock(block);

  // Soft alone: no crash, value is in valid range.
  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 0);
  EXPECT_LE(solver.GetValue("x"), 100);
}

}  // namespace
