#include <gtest/gtest.h>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

ConstraintSolver UniqueSolver(RandQualifier b_qualifier) {
  ConstraintSolver solver(7);
  RandVariable a;
  a.name = "a";
  a.min_val = 0;
  a.max_val = 3;
  solver.AddVariable(a);
  RandVariable b;
  b.name = "b";
  b.qualifier = b_qualifier;
  b.min_val = 0;
  b.max_val = 3;
  solver.AddVariable(b);
  ConstraintBlock block;
  block.name = "u";
  ConstraintExpr u;
  u.kind = ConstraintKind::kUnique;
  u.unique_vars = {"a", "b"};
  block.constraints.push_back(u);
  solver.AddConstraintBlock(block);
  return solver;
}

TEST(ConstraintUniqueSolver, RandcMemberFailsTheSolve) {
  ConstraintSolver with_randc = UniqueSolver(RandQualifier::kRandc);
  EXPECT_FALSE(with_randc.Solve());
  ConstraintSolver with_rand = UniqueSolver(RandQualifier::kRand);
  ASSERT_TRUE(with_rand.Solve());
  EXPECT_NE(with_rand.GetValue("a"), with_rand.GetValue("b"));
}

}  // namespace
