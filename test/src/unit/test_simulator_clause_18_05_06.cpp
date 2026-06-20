#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_map>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// 18.5.6: when the if condition is true, every constraint in the then set shall
// be satisfied. With mode pinned to 1 the condition holds, so data must fall in
// the then branch's range and the else branch's value is not imposed.
TEST(ConstraintIfElse, ThenBranchAppliedWhenConditionTrue) {
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

  ConstraintBlock pin;
  pin.name = "c_mode";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "mode";
  eq.lo = 1;
  pin.constraints.push_back(eq);
  solver.AddConstraintBlock(pin);

  ConstraintBlock guard;
  guard.name = "c_ifelse";
  ConstraintExpr ife;
  ife.kind = ConstraintKind::kIfElse;
  ife.cond_var = "mode";
  ife.cond_value = 1;
  ConstraintExpr then_c;
  then_c.kind = ConstraintKind::kRange;
  then_c.var_name = "data";
  then_c.lo = 10;
  then_c.hi = 20;
  ife.sub_constraints.push_back(then_c);
  ConstraintExpr else_c;
  else_c.kind = ConstraintKind::kEqual;
  else_c.var_name = "data";
  else_c.lo = 99;
  ife.else_constraints.push_back(else_c);
  guard.constraints.push_back(ife);
  solver.AddConstraintBlock(guard);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("mode"), 1);
  EXPECT_GE(solver.GetValue("data"), 10);
  EXPECT_LE(solver.GetValue("data"), 20);
}

// 18.5.6: when the condition is false, every constraint in the optional else
// set shall be satisfied. With mode pinned to 0 the condition (mode == 1)
// fails, so data must take the else branch's value rather than the then
// branch's range.
TEST(ConstraintIfElse, ElseBranchAppliedWhenConditionFalse) {
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

  ConstraintBlock pin;
  pin.name = "c_mode";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "mode";
  eq.lo = 0;
  pin.constraints.push_back(eq);
  solver.AddConstraintBlock(pin);

  ConstraintBlock guard;
  guard.name = "c_ifelse";
  ConstraintExpr ife;
  ife.kind = ConstraintKind::kIfElse;
  ife.cond_var = "mode";
  ife.cond_value = 1;
  ConstraintExpr then_c;
  then_c.kind = ConstraintKind::kRange;
  then_c.var_name = "data";
  then_c.lo = 10;
  then_c.hi = 20;
  ife.sub_constraints.push_back(then_c);
  ConstraintExpr else_c;
  else_c.kind = ConstraintKind::kEqual;
  else_c.var_name = "data";
  else_c.lo = 99;
  ife.else_constraints.push_back(else_c);
  guard.constraints.push_back(ife);
  solver.AddConstraintBlock(guard);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("mode"), 0);
  EXPECT_EQ(solver.GetValue("data"), 99);
}

// 18.5.6: the else part is optional. When the condition is false and no else
// set is present, nothing is imposed on the guarded variable, which is then
// free to range over its full domain.
TEST(ConstraintIfElse, AbsentElseImposesNothing) {
  ConstraintSolver solver(7);
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

  ConstraintBlock pin;
  pin.name = "c_mode";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "mode";
  eq.lo = 0;
  pin.constraints.push_back(eq);
  solver.AddConstraintBlock(pin);

  ConstraintBlock guard;
  guard.name = "c_ifelse";
  ConstraintExpr ife;
  ife.kind = ConstraintKind::kIfElse;
  ife.cond_var = "mode";
  ife.cond_value = 1;
  ConstraintExpr then_c;
  then_c.kind = ConstraintKind::kEqual;
  then_c.var_name = "data";
  then_c.lo = 5;
  ife.sub_constraints.push_back(then_c);
  guard.constraints.push_back(ife);
  solver.AddConstraintBlock(guard);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("mode"), 0);
  // The then-branch value (5) is not forced; data merely stays within range.
  EXPECT_GE(solver.GetValue("data"), 0);
  EXPECT_LE(solver.GetValue("data"), 255);
}

// 18.5.6: the if condition can be any integral or real expression, not just an
// equality test. A general predicate over the current values selects the
// branch; here "mode > 5" holds, so the then set's range applies to data.
TEST(ConstraintIfElse, ConditionMayBeArbitraryExpression) {
  ConstraintSolver solver(42);
  RandVariable vmode;
  vmode.name = "mode";
  vmode.min_val = 10;
  vmode.max_val = 10;
  solver.AddVariable(vmode);

  RandVariable vdata;
  vdata.name = "data";
  vdata.min_val = 0;
  vdata.max_val = 255;
  solver.AddVariable(vdata);

  ConstraintBlock guard;
  guard.name = "c_ifelse";
  ConstraintExpr ife;
  ife.kind = ConstraintKind::kIfElse;
  ife.cond_fn = [](const std::unordered_map<std::string, int64_t>& v) {
    auto it = v.find("mode");
    return it != v.end() && it->second > 5;
  };
  ConstraintExpr then_c;
  then_c.kind = ConstraintKind::kRange;
  then_c.var_name = "data";
  then_c.lo = 10;
  then_c.hi = 20;
  ife.sub_constraints.push_back(then_c);
  ConstraintExpr else_c;
  else_c.kind = ConstraintKind::kEqual;
  else_c.var_name = "data";
  else_c.lo = 99;
  ife.else_constraints.push_back(else_c);
  guard.constraints.push_back(ife);
  solver.AddConstraintBlock(guard);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("data"), 10);
  EXPECT_LE(solver.GetValue("data"), 20);
}

// 18.5.6: the condition and the guarded set are interdependent and constrain
// each other. Here mode is left free, but data is pinned to 99. The then set
// (data in [10,20]) is then unsatisfiable, so the condition must come out false
// for the whole constraint to hold: the guarded set drives mode away from 1.
TEST(ConstraintIfElse, GuardedSetConstrainsCondition) {
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

  ConstraintBlock pin;
  pin.name = "c_data";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "data";
  eq.lo = 99;
  pin.constraints.push_back(eq);
  solver.AddConstraintBlock(pin);

  ConstraintBlock guard;
  guard.name = "c_ifelse";
  ConstraintExpr ife;
  ife.kind = ConstraintKind::kIfElse;
  ife.cond_var = "mode";
  ife.cond_value = 1;
  ConstraintExpr then_c;
  then_c.kind = ConstraintKind::kRange;
  then_c.var_name = "data";
  then_c.lo = 10;
  then_c.hi = 20;
  ife.sub_constraints.push_back(then_c);
  guard.constraints.push_back(ife);
  solver.AddConstraintBlock(guard);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("data"), 99);
  EXPECT_NE(solver.GetValue("mode"), 1);
}

// 18.5.6: an "else if" chain is an if-else whose else set is itself another
// if-else. When the outer condition fails and the inner one holds, the inner
// then set governs. With mode pinned to 2 the outer test (mode == 1) is false
// and the inner test (mode == 2) is true, so data takes the inner range.
TEST(ConstraintIfElse, ElseIfChainSelectsMatchingBranch) {
  ConstraintSolver solver(42);
  RandVariable vmode;
  vmode.name = "mode";
  vmode.min_val = 0;
  vmode.max_val = 2;
  solver.AddVariable(vmode);

  RandVariable vdata;
  vdata.name = "data";
  vdata.min_val = 0;
  vdata.max_val = 255;
  solver.AddVariable(vdata);

  ConstraintBlock pin;
  pin.name = "c_mode";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "mode";
  eq.lo = 2;
  pin.constraints.push_back(eq);
  solver.AddConstraintBlock(pin);

  ConstraintBlock guard;
  guard.name = "c_ifelse";
  ConstraintExpr outer;
  outer.kind = ConstraintKind::kIfElse;
  outer.cond_var = "mode";
  outer.cond_value = 1;
  ConstraintExpr outer_then;
  outer_then.kind = ConstraintKind::kRange;
  outer_then.var_name = "data";
  outer_then.lo = 0;
  outer_then.hi = 9;
  outer.sub_constraints.push_back(outer_then);

  ConstraintExpr inner;
  inner.kind = ConstraintKind::kIfElse;
  inner.cond_var = "mode";
  inner.cond_value = 2;
  ConstraintExpr inner_then;
  inner_then.kind = ConstraintKind::kRange;
  inner_then.var_name = "data";
  inner_then.lo = 100;
  inner_then.hi = 200;
  inner.sub_constraints.push_back(inner_then);
  outer.else_constraints.push_back(inner);

  guard.constraints.push_back(outer);
  solver.AddConstraintBlock(guard);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("mode"), 2);
  EXPECT_GE(solver.GetValue("data"), 100);
  EXPECT_LE(solver.GetValue("data"), 200);
}

// 18.5.6: when the condition is true, every constraint in the then set shall be
// satisfied. Here the surrounding constraints pin the condition true (mode ==
// 1) and pin data to 99, a value the then set's range [10,20] forbids. The
// condition cannot be made false to escape the then set, so no assignment
// satisfies the if constraint and the solver shall report failure.
TEST(ConstraintIfElse, UnsatisfiableThenSetUnderForcedConditionFails) {
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

  ConstraintBlock pin;
  pin.name = "c_pin";
  ConstraintExpr pin_mode;
  pin_mode.kind = ConstraintKind::kEqual;
  pin_mode.var_name = "mode";
  pin_mode.lo = 1;
  pin.constraints.push_back(pin_mode);
  ConstraintExpr pin_data;
  pin_data.kind = ConstraintKind::kEqual;
  pin_data.var_name = "data";
  pin_data.lo = 99;
  pin.constraints.push_back(pin_data);
  solver.AddConstraintBlock(pin);

  ConstraintBlock guard;
  guard.name = "c_ifelse";
  ConstraintExpr ife;
  ife.kind = ConstraintKind::kIfElse;
  ife.cond_var = "mode";
  ife.cond_value = 1;
  ConstraintExpr then_c;
  then_c.kind = ConstraintKind::kRange;
  then_c.var_name = "data";
  then_c.lo = 10;
  then_c.hi = 20;
  ife.sub_constraints.push_back(then_c);
  guard.constraints.push_back(ife);
  solver.AddConstraintBlock(guard);

  EXPECT_FALSE(solver.Solve());
}

// 18.5.6: the condition and the guarded sets are interdependent, and the else
// set takes part in that coupling as well. With data pinned to 99 the then set
// (data == 99) is satisfiable only when the condition holds, while the else set
// (data in [10,20]) cannot be satisfied at all. The solver must therefore drive
// the condition true, choosing mode == 1, so the else set is never imposed.
TEST(ConstraintIfElse, ElseSetConstrainsConditionTrue) {
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

  ConstraintBlock pin;
  pin.name = "c_data";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "data";
  eq.lo = 99;
  pin.constraints.push_back(eq);
  solver.AddConstraintBlock(pin);

  ConstraintBlock guard;
  guard.name = "c_ifelse";
  ConstraintExpr ife;
  ife.kind = ConstraintKind::kIfElse;
  ife.cond_var = "mode";
  ife.cond_value = 1;
  ConstraintExpr then_c;
  then_c.kind = ConstraintKind::kEqual;
  then_c.var_name = "data";
  then_c.lo = 99;
  ife.sub_constraints.push_back(then_c);
  ConstraintExpr else_c;
  else_c.kind = ConstraintKind::kRange;
  else_c.var_name = "data";
  else_c.lo = 10;
  else_c.hi = 20;
  ife.else_constraints.push_back(else_c);
  guard.constraints.push_back(ife);
  solver.AddConstraintBlock(guard);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("data"), 99);
  EXPECT_EQ(solver.GetValue("mode"), 1);
}

}  // namespace
