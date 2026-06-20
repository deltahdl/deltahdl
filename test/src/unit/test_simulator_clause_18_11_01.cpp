#include <gtest/gtest.h>

#include <cstdint>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// 18.11.1: passing null to randomize() indicates no random variables for the
// duration of the call, so even a variable declared rand is held at its current
// value as a state variable. Here x currently satisfies the constraint, so the
// inline constraint checker returns 1 and leaves x untouched — a generator
// would have drawn a fresh value, but the checker draws nothing.
TEST(InlineConstraintChecker, NullArgumentHoldsRandVariableAsState) {
  ConstraintSolver solver(42);

  RandVariable x;
  x.name = "x";
  x.qualifier = RandQualifier::kRand;
  x.min_val = 0;
  x.max_val = 100;
  x.value = 7;  // current value, satisfies x > 5 below
  solver.AddVariable(x);

  ConstraintExpr c;
  c.kind = ConstraintKind::kGreaterThan;
  c.var_name = "x";
  c.lo = 5;
  ConstraintBlock block;
  block.name = "c_gt";
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  EXPECT_TRUE(solver.InlineConstraintCheck());
  EXPECT_EQ(solver.GetValue("x"), 7);  // unchanged: treated as a state variable
}

// 18.11.1: a checker evaluates all constraints against the current values and
// returns 0 as soon as one is not satisfied. The rand variable's current value
// violates the constraint; because null suppresses randomization, the checker
// cannot move x into a satisfying value — it simply reports the failure and
// leaves x as it found it.
TEST(InlineConstraintChecker, NullArgumentReturnsZeroWhenConstraintViolated) {
  ConstraintSolver solver(42);

  RandVariable x;
  x.name = "x";
  x.qualifier = RandQualifier::kRand;
  x.min_val = 0;
  x.max_val = 100;
  x.value = 3;  // current value, violates x > 5
  solver.AddVariable(x);

  ConstraintExpr c;
  c.kind = ConstraintKind::kGreaterThan;
  c.var_name = "x";
  c.lo = 5;
  ConstraintBlock block;
  block.name = "c_gt";
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.InlineConstraintCheck());
  EXPECT_EQ(solver.GetValue("x"), 3);  // unchanged: never randomized
}

// 18.11.1: the null argument turns randomize() into a checker rather than a
// generator. Repeated calls over a wide domain never alter the rand variable —
// a generator would almost certainly produce a different value at least once,
// whereas the checker deterministically reports the same current value every
// time.
TEST(InlineConstraintChecker, NullArgumentNeverRandomizesAcrossCalls) {
  ConstraintSolver solver(123);

  RandVariable x;
  x.name = "x";
  x.qualifier = RandQualifier::kRand;
  x.min_val = 0;
  x.max_val = 1000;
  x.value = 314;
  solver.AddVariable(x);

  for (int i = 0; i < 20; ++i) {
    EXPECT_TRUE(solver.InlineConstraintCheck());
    EXPECT_EQ(solver.GetValue("x"), 314);
  }
}

// 18.11.1: even a randc variable is held as a state variable under the null
// argument — the inline checker does not cycle it through its domain, it simply
// checks the current value. Here the randc variable's value satisfies the
// constraint and is reported unchanged.
TEST(InlineConstraintChecker, NullArgumentHoldsRandcVariableAsState) {
  ConstraintSolver solver(7);

  RandVariable c;
  c.name = "c";
  c.qualifier = RandQualifier::kRandc;
  c.min_val = 0;
  c.max_val = 3;
  c.value = 2;
  solver.AddVariable(c);

  ConstraintExpr lt;
  lt.kind = ConstraintKind::kLessThan;
  lt.var_name = "c";
  lt.lo = 3;
  ConstraintBlock block;
  block.name = "c_lt";
  block.constraints.push_back(lt);
  solver.AddConstraintBlock(block);

  EXPECT_TRUE(solver.InlineConstraintCheck());
  EXPECT_EQ(solver.GetValue("c"), 2);  // not cycled: held as a state variable
}

// 18.11.1: a class that declares no random variables makes randomize() behave
// as a checker even without the null argument. Modeled here with a plain
// property (no rand qualifier): the inline checker evaluates the constraint
// against its current value and returns 1 when it holds.
TEST(InlineConstraintChecker, NoRandomVariablesActsAsChecker) {
  ConstraintSolver solver(1);

  RandVariable s;
  s.name = "s";
  s.qualifier = RandQualifier::kNone;
  s.value = 4;
  solver.AddVariable(s);

  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "s";
  eq.lo = 4;
  ConstraintBlock block;
  block.name = "c_eq";
  block.constraints.push_back(eq);
  solver.AddConstraintBlock(block);

  EXPECT_TRUE(solver.InlineConstraintCheck());

  // Move the property off the constrained value: the checker now reports 0,
  // confirming it tests the live value rather than solving for a new one.
  solver.SetValue("s", 9);
  EXPECT_FALSE(solver.InlineConstraintCheck());
  EXPECT_EQ(solver.GetValue("s"), 9);
}

// 18.11.1: the checker evaluates every constraint, including a with-clause
// relation passed alongside the object's own constraint blocks. Both must hold
// against the current values for the call to return 1.
TEST(InlineConstraintChecker, ChecksWithClauseConstraintsToo) {
  ConstraintSolver solver(2);

  RandVariable x;
  x.name = "x";
  x.qualifier = RandQualifier::kRand;
  x.value = 10;
  solver.AddVariable(x);

  // A custom with-clause constraint requiring x to be even.
  ConstraintExpr even;
  even.kind = ConstraintKind::kCustom;
  even.eval_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    auto it = vals.find("x");
    return it != vals.end() && (it->second % 2 == 0);
  };

  EXPECT_TRUE(solver.InlineConstraintCheck({even}));  // 10 is even

  solver.SetValue("x", 11);
  EXPECT_FALSE(solver.InlineConstraintCheck({even}));  // 11 is odd
  EXPECT_EQ(solver.GetValue("x"), 11);                 // never randomized
}

// 18.11.1: the null argument makes every class member a state variable, not
// just one. With two rand variables joined by a single relation, the checker
// evaluates that relation against both current values and draws a fresh value
// for neither. The relation holds here, so the call returns 1 and both
// variables keep the values they came in with; moving one value so the relation
// fails makes the checker report 0 while still leaving both untouched.
TEST(InlineConstraintChecker, NullArgumentHoldsAllVariablesAsState) {
  ConstraintSolver solver(55);

  RandVariable x;
  x.name = "x";
  x.qualifier = RandQualifier::kRand;
  x.min_val = 0;
  x.max_val = 100;
  x.value = 3;
  solver.AddVariable(x);

  RandVariable y;
  y.name = "y";
  y.qualifier = RandQualifier::kRand;
  y.min_val = 0;
  y.max_val = 100;
  y.value = 8;
  solver.AddVariable(y);

  // A relation between the two random variables: x must stay below y.
  ConstraintExpr rel;
  rel.kind = ConstraintKind::kCustom;
  rel.eval_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    auto ix = vals.find("x");
    auto iy = vals.find("y");
    return ix != vals.end() && iy != vals.end() && ix->second < iy->second;
  };
  ConstraintBlock block;
  block.name = "c_rel";
  block.constraints.push_back(rel);
  solver.AddConstraintBlock(block);

  EXPECT_TRUE(solver.InlineConstraintCheck());
  EXPECT_EQ(solver.GetValue("x"), 3);  // held as a state variable
  EXPECT_EQ(solver.GetValue("y"), 8);  // held as a state variable

  // Move x past y so the relation no longer holds: the checker reports 0 and
  // still leaves both variables exactly as they were — it never solves for a
  // new assignment.
  solver.SetValue("x", 9);
  EXPECT_FALSE(solver.InlineConstraintCheck());
  EXPECT_EQ(solver.GetValue("x"), 9);
  EXPECT_EQ(solver.GetValue("y"), 8);
}

// 18.11.1: a checker returns 1 when every constraint is satisfied. With no
// constraint blocks at all there is nothing that can fail, so the inline
// checker reports success at this boundary while still drawing no value for the
// rand variable, which keeps its current value.
TEST(InlineConstraintChecker, NullArgumentWithNoConstraintsReturnsOne) {
  ConstraintSolver solver(99);

  RandVariable x;
  x.name = "x";
  x.qualifier = RandQualifier::kRand;
  x.min_val = 0;
  x.max_val = 100;
  x.value = 42;
  solver.AddVariable(x);

  // No constraint blocks added: the checker has nothing to test and so reports
  // success, without ever solving for a fresh value.
  EXPECT_TRUE(solver.InlineConstraintCheck());
  EXPECT_EQ(solver.GetValue("x"), 42);
}

}  // namespace
