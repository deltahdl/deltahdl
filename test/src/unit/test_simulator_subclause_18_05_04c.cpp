#include <gtest/gtest.h>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// These tests drive the constraint solver directly with a uniqueness group
// (18.5.4) holding a randc member. The elaborator rejects such a group in
// every source whose receiver class it can name, so the solver's own refusal
// is reached from a hand-built solver state rather than from source.

// A solver holding rand a and a b declared `b_qualifier`, both over 0..3,
// under one block constraining {a, b} to be unique.
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

// 18.5.4: no randc variable shall appear in the group, so a group naming one
// is illegal and the solve fails; the same group with b rand solves, with a
// and b distinct.
TEST(ConstraintUniqueSolver, RandcMemberFailsTheSolve) {
  ConstraintSolver with_randc = UniqueSolver(RandQualifier::kRandc);
  EXPECT_FALSE(with_randc.Solve());
  ConstraintSolver with_rand = UniqueSolver(RandQualifier::kRand);
  ASSERT_TRUE(with_rand.Solve());
  EXPECT_NE(with_rand.GetValue("a"), with_rand.GetValue("b"));
}

}  // namespace
