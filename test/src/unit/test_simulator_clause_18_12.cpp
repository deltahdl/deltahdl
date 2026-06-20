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

TEST(Constraint, StdRandomizeStandalone) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "local_var";
  v.min_val = 0;
  v.max_val = 255;
  solver.AddVariable(v);

  ConstraintExpr c;
  c.kind = ConstraintKind::kRange;
  c.var_name = "local_var";
  c.lo = 100;
  c.hi = 200;

  ASSERT_TRUE(solver.SolveWith({c}));
  int64_t val = solver.GetValue("local_var");
  EXPECT_GE(val, 100);
  EXPECT_LE(val, 200);
}

// 18.12: the scope randomize function returns 1 only when it sets all the
// random variables to valid values. With two random variables that each carry a
// satisfiable range, the call succeeds and both land inside their own ranges,
// confirming every random variable — not just one — is assigned a valid value.
TEST(ScopeRandomize, SetsAllRandomVariablesOnSuccess) {
  ConstraintSolver solver(99);
  RandVariable a;
  a.name = "a";
  a.min_val = 0;
  a.max_val = 100;
  solver.AddVariable(a);
  RandVariable b;
  b.name = "b";
  b.min_val = 0;
  b.max_val = 100;
  solver.AddVariable(b);

  ConstraintExpr ca;
  ca.kind = ConstraintKind::kRange;
  ca.var_name = "a";
  ca.lo = 0;
  ca.hi = 50;
  ConstraintExpr cb;
  cb.kind = ConstraintKind::kRange;
  cb.var_name = "b";
  cb.lo = 50;
  cb.hi = 100;

  ASSERT_TRUE(solver.SolveWith({ca, cb}));
  EXPECT_GE(solver.GetValue("a"), 0);
  EXPECT_LE(solver.GetValue("a"), 50);
  EXPECT_GE(solver.GetValue("b"), 50);
  EXPECT_LE(solver.GetValue("b"), 100);
}

// 18.12: otherwise it returns 0. When no value in the variable's domain can
// satisfy the constraints, the scope randomize fails and reports false.
TEST(ScopeRandomize, ReturnsFalseWhenUnsatisfiable) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "a";
  v.min_val = 0;
  v.max_val = 50;
  solver.AddVariable(v);

  // Demand a value outside the variable's domain: no assignment can satisfy it.
  ConstraintExpr c;
  c.kind = ConstraintKind::kRange;
  c.var_name = "a";
  c.lo = 100;
  c.hi = 200;

  EXPECT_FALSE(solver.SolveWith({c}));
}

// 18.12: a scope randomize called with no random-variable argument shall not
// change the value of any variable but instead check its constraints. With the
// current values already satisfying the relation, the checker returns true and
// leaves every variable exactly as it was.
TEST(ScopeRandomize, NoArgCheckerPassesWithoutChangingVariables) {
  ConstraintSolver solver(1);
  RandVariable a;
  a.name = "a";
  a.min_val = 0;
  a.max_val = 100;
  solver.AddVariable(a);
  RandVariable b;
  b.name = "b";
  b.min_val = 0;
  b.max_val = 100;
  solver.AddVariable(b);

  solver.SetValue("a", 3);
  solver.SetValue("b", 9);

  // Check a < b against the current values; the relation holds.
  ConstraintExpr c;
  c.kind = ConstraintKind::kLessThan;
  c.var_name = "a";
  c.lo = 9;  // a < 9 holds for a == 3

  EXPECT_TRUE(solver.Check({c}));
  // No variable was randomized: both keep their pre-check values.
  EXPECT_EQ(solver.GetValue("a"), 3);
  EXPECT_EQ(solver.GetValue("b"), 9);
}

// 18.12: every constraint expression of a no-argument scope randomize is
// evaluated, and if one or more of them is false (0) the call returns 0. Here
// the current value violates the relation, so the checker reports false and
// still changes nothing.
TEST(ScopeRandomize, NoArgCheckerFailsWhenConstraintFalse) {
  ConstraintSolver solver(1);
  RandVariable a;
  a.name = "a";
  a.min_val = 0;
  a.max_val = 100;
  solver.AddVariable(a);

  solver.SetValue("a", 42);

  // Require a < 10, which 42 does not satisfy.
  ConstraintExpr c;
  c.kind = ConstraintKind::kLessThan;
  c.var_name = "a";
  c.lo = 10;

  EXPECT_FALSE(solver.Check({c}));
  EXPECT_EQ(solver.GetValue("a"), 42);  // unchanged by the failed check
}

// 18.12: "if one or more of those expressions evaluates to false" — a single
// false expression among several true ones is enough to make the checker
// return 0, confirming all expressions are evaluated rather than only the
// first.
TEST(ScopeRandomize, NoArgCheckerFailsIfAnyExpressionFalse) {
  ConstraintSolver solver(1);
  RandVariable a;
  a.name = "a";
  a.min_val = 0;
  a.max_val = 100;
  solver.AddVariable(a);

  solver.SetValue("a", 5);

  ConstraintExpr ok;  // 5 > 0 holds
  ok.kind = ConstraintKind::kGreaterThan;
  ok.var_name = "a";
  ok.lo = 0;

  ConstraintExpr bad;  // 5 > 10 does not hold
  bad.kind = ConstraintKind::kGreaterThan;
  bad.var_name = "a";
  bad.lo = 10;

  EXPECT_FALSE(solver.Check({ok, bad}));
  // All true expressions still pass on their own.
  EXPECT_TRUE(solver.Check({ok}));
}

// 18.12: when a no-argument scope randomize has no constraint expression that
// evaluates to false — here there are no constraints at all — none of them is
// false, so the checker takes the "otherwise" branch and returns 1 (true). It
// still assigns nothing, leaving the variable at its current value.
TEST(ScopeRandomize, NoArgCheckerReturnsTrueWithNoConstraints) {
  ConstraintSolver solver(1);
  RandVariable a;
  a.name = "a";
  a.min_val = 0;
  a.max_val = 100;
  solver.AddVariable(a);

  solver.SetValue("a", 17);

  EXPECT_TRUE(solver.Check());
  EXPECT_EQ(solver.GetValue("a"), 17);  // unchanged by the check
}

}  // namespace
