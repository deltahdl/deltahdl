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

  // 18.5.13: with no hard constraint to conflict with, the soft constraint can
  // be satisfied, so the solver shall honor it rather than discard it.
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 42);
}

// 18.5.13: a soft constraint that is jointly satisfiable with the active hard
// constraints shall be satisfied. Here the soft preference x == 50 sits inside
// the hard range [40, 60], so the solver produces 50 rather than some other
// in-range value.
TEST(Constraint, SoftConstraintHonoredWhenCompatibleWithHard) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock b_hard;
  b_hard.name = "c_range";
  ConstraintExpr hc;
  hc.kind = ConstraintKind::kRange;
  hc.var_name = "x";
  hc.lo = 40;
  hc.hi = 60;
  b_hard.constraints.push_back(hc);
  solver.AddConstraintBlock(b_hard);

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

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 50);
}

// 18.5.13: when a soft constraint conflicts with the hard constraints, it is
// discarded and treated as if replaced by the value 1 (true): randomization
// still succeeds (the hard constraint is satisfied) and the discarded soft
// constraint need not hold. The soft x == 50 conflicts with the hard range
// [10, 20], so the solver discards it and returns an in-range value.
TEST(Constraint, ConflictingSoftConstraintDiscardedAndTreatedAsTrue) {
  ConstraintSolver solver(99);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock b_hard;
  b_hard.name = "c_range";
  ConstraintExpr hc;
  hc.kind = ConstraintKind::kRange;
  hc.var_name = "x";
  hc.lo = 10;
  hc.hi = 20;
  b_hard.constraints.push_back(hc);
  solver.AddConstraintBlock(b_hard);

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

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 10);
  EXPECT_LE(solver.GetValue("x"), 20);
  EXPECT_NE(solver.GetValue("x"), 50);
}

// 18.5.13: hard constraints differ from soft ones in that the solver must
// always satisfy them; when they cannot all hold simultaneously, randomization
// fails rather than relaxing any of them. The two mutually exclusive hard
// equalities x == 10 and x == 20 can never both hold, so the solve fails.
TEST(Constraint, UnsatisfiableHardConstraintsFailSolve) {
  ConstraintSolver solver(3);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_hard";
  ConstraintExpr a;
  a.kind = ConstraintKind::kEqual;
  a.var_name = "x";
  a.lo = 10;
  block.constraints.push_back(a);
  ConstraintExpr b;
  b.kind = ConstraintKind::kEqual;
  b.var_name = "x";
  b.lo = 20;
  block.constraints.push_back(b);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
}

// 18.5.13: when two or more soft constraints cannot be satisfied
// simultaneously, one or more of them shall be discarded so that a solution is
// still found (which ones is governed by the priorities of 18.5.13.1). The two
// mutually exclusive soft equalities x == 10 and x == 20 cannot both hold, yet
// unlike the hard case the solve succeeds because the conflict is resolved by
// discarding soft constraints.
TEST(Constraint, ConflictingSoftConstraintsResolvedByDiscarding) {
  ConstraintSolver solver(3);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_soft";
  ConstraintExpr inner_a;
  inner_a.kind = ConstraintKind::kEqual;
  inner_a.var_name = "x";
  inner_a.lo = 10;
  ConstraintExpr sa;
  sa.kind = ConstraintKind::kSoft;
  sa.inner = &inner_a;
  sa.var_name = "x";
  block.constraints.push_back(sa);
  ConstraintExpr inner_b;
  inner_b.kind = ConstraintKind::kEqual;
  inner_b.var_name = "x";
  inner_b.lo = 20;
  ConstraintExpr sb;
  sb.kind = ConstraintKind::kSoft;
  sb.inner = &inner_b;
  sb.var_name = "x";
  block.constraints.push_back(sb);
  solver.AddConstraintBlock(block);

  EXPECT_TRUE(solver.Solve());
}

// 18.5.13: a discarded soft constraint has no effect on the solution
// distribution. It must not pin the variable to its preferred value, and it
// must not remove any value the hard constraints still allow. Here the hard
// range confines x to {0, 1} while the soft preference x == 2 conflicts with
// it and is therefore discarded. Across many randomizations the solver keeps
// producing both feasible values and never the discarded preference, so the
// discarded soft constraint neither biases nor narrows the distribution.
TEST(Constraint, DiscardedSoftConstraintDoesNotBiasDistribution) {
  ConstraintSolver solver(123);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 3;
  solver.AddVariable(v);

  ConstraintBlock b_hard;
  b_hard.name = "c_range";
  ConstraintExpr hc;
  hc.kind = ConstraintKind::kRange;
  hc.var_name = "x";
  hc.lo = 0;
  hc.hi = 1;
  b_hard.constraints.push_back(hc);
  solver.AddConstraintBlock(b_hard);

  ConstraintBlock b_soft;
  b_soft.name = "c_soft";
  ConstraintExpr inner_expr;
  inner_expr.kind = ConstraintKind::kEqual;
  inner_expr.var_name = "x";
  inner_expr.lo = 2;
  ConstraintExpr sc;
  sc.kind = ConstraintKind::kSoft;
  sc.inner = &inner_expr;
  sc.var_name = "x";
  b_soft.constraints.push_back(sc);
  solver.AddConstraintBlock(b_soft);

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 100; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t x = solver.GetValue("x");
    EXPECT_GE(x, 0);
    EXPECT_LE(x, 1);
    // The discarded preference is never honored.
    EXPECT_NE(x, 2);
    seen.insert(x);
  }
  // Both hard-feasible values still occur: the discarded soft neither pinned
  // the result to a single value nor removed any allowed one.
  EXPECT_EQ(seen.size(), 2u);
}

}  // namespace
