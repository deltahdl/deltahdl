// §18.5.6: if–else constraints

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
// §18.5.6: Implication constraints (if-else)
// =============================================================================
TEST(Constraint, ImplicationTrue) {
  ConstraintSolver solver(42);
  RandVariable vmode;
  vmode.name = "mode";
  vmode.min_val = 0;
  vmode.max_val = 1;
  solver.AddVariable(vmode);

  RandVariable vdata;
  vdata.name = "data";
  vdata.min_val = 0;
  vdata.max_val = 255;
  solver.AddVariable(vdata);

  ConstraintBlock b1;
  b1.name = "c_mode";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "mode";
  eq.lo = 1;
  b1.constraints.push_back(eq);
  solver.AddConstraintBlock(b1);

  ConstraintBlock b2;
  b2.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "mode";
  impl.cond_value = 1;
  ConstraintExpr sub;
  sub.kind = ConstraintKind::kRange;
  sub.var_name = "data";
  sub.lo = 10;
  sub.hi = 20;
  impl.sub_constraints.push_back(sub);
  b2.constraints.push_back(impl);
  solver.AddConstraintBlock(b2);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("mode"), 1);
  EXPECT_GE(solver.GetValue("data"), 10);
  EXPECT_LE(solver.GetValue("data"), 20);
}

TEST(Constraint, ImplicationFalseAntecedent) {
  ConstraintSolver solver(42);
  RandVariable vmode;
  vmode.name = "mode";
  vmode.min_val = 0;
  vmode.max_val = 255;
  solver.AddVariable(vmode);

  RandVariable vdata;
  vdata.name = "data";
  vdata.min_val = 0;
  vdata.max_val = 255;
  solver.AddVariable(vdata);

  ConstraintBlock b1;
  b1.name = "c_mode";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "mode";
  eq.lo = 0;
  b1.constraints.push_back(eq);
  solver.AddConstraintBlock(b1);

  ConstraintBlock b2;
  b2.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "mode";
  impl.cond_value = 1;
  ConstraintExpr sub;
  sub.kind = ConstraintKind::kEqual;
  sub.var_name = "data";
  sub.lo = 99;
  impl.sub_constraints.push_back(sub);
  b2.constraints.push_back(impl);
  solver.AddConstraintBlock(b2);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("mode"), 0);
  EXPECT_GE(solver.GetValue("data"), 0);
  EXPECT_LE(solver.GetValue("data"), 255);
}

}  // namespace
