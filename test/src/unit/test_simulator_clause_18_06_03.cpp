#include <gtest/gtest.h>

#include <cstdint>
#include <memory>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// 18.6.3: random variables declared static are shared by all instances of the
// class in which they are declared, and each randomize() changes the variable
// in every class instance. Two solvers stand in for two instances; both name
// one shared static variable. Randomizing one instance updates the shared value
// that every instance observes, and randomizing the other changes it for both
// again. Each instance is forced to a distinct value so the propagation is
// unambiguous rather than coincidental.
TEST(BehaviorOfRandomizationMethods, StaticVariableSharedAcrossInstances) {
  auto shared = std::make_shared<int64_t>(0);

  auto make_static = [&]() {
    RandVariable v;
    v.name = "x";
    v.min_val = 0;
    v.max_val = 1000;
    v.is_static = true;
    v.shared_value = shared;
    return v;
  };

  ConstraintSolver inst_a(5);
  ConstraintSolver inst_b(9);
  inst_a.AddVariable(make_static());
  inst_b.AddVariable(make_static());

  // Instance A pins the shared variable to 5.
  ConstraintBlock pin_a;
  pin_a.name = "ca";
  ConstraintExpr eq_a;
  eq_a.kind = ConstraintKind::kEqual;
  eq_a.var_name = "x";
  eq_a.lo = 5;
  pin_a.constraints.push_back(eq_a);
  inst_a.AddConstraintBlock(pin_a);

  // Instance B pins the shared variable to 9.
  ConstraintBlock pin_b;
  pin_b.name = "cb";
  ConstraintExpr eq_b;
  eq_b.kind = ConstraintKind::kEqual;
  eq_b.var_name = "x";
  eq_b.lo = 9;
  pin_b.constraints.push_back(eq_b);
  inst_b.AddConstraintBlock(pin_b);

  // Randomizing instance A sets the static variable to 5 for every instance.
  ASSERT_TRUE(inst_a.Solve());
  EXPECT_EQ(inst_a.GetValue("x"), 5);
  EXPECT_EQ(inst_b.GetValue("x"), 5);

  // Randomizing instance B then changes it to 9 for every instance.
  ASSERT_TRUE(inst_b.Solve());
  EXPECT_EQ(inst_b.GetValue("x"), 9);
  EXPECT_EQ(inst_a.GetValue("x"), 9);
}

// 18.6.3: if randomize() fails, the constraints are infeasible and the random
// variables retain their previous values. A first solve assigns a value; a
// second solve, made infeasible by pinning the variable to two different
// values at once, fails — and the variable still holds the value from the
// successful solve rather than being cleared or left in a partial state.
TEST(BehaviorOfRandomizationMethods, FailedRandomizeRetainsPreviousValue) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ASSERT_TRUE(solver.Solve());
  const int64_t prev = solver.GetValue("x");

  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr eq_lo;
  eq_lo.kind = ConstraintKind::kEqual;
  eq_lo.var_name = "x";
  eq_lo.lo = 10;
  block.constraints.push_back(eq_lo);
  ConstraintExpr eq_hi;
  eq_hi.kind = ConstraintKind::kEqual;
  eq_hi.var_name = "x";
  eq_hi.lo = 20;
  block.constraints.push_back(eq_hi);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
  // The variable kept the value the previous, successful randomize() produced.
  EXPECT_EQ(solver.GetValue("x"), prev);
}

// 18.6.3: if randomize() fails, post_randomize() is not called. A post hook is
// registered and an infeasible constraint set is imposed; the failing solve
// must leave the hook un-fired. The companion successful solve confirms the
// same hook does run on success, so its absence on failure is the rule at work
// rather than a hook that never fires.
TEST(BehaviorOfRandomizationMethods, PostRandomizeNotCalledOnFailure) {
  ConstraintSolver solver(7);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  int post_calls = 0;
  solver.SetPostRandomize([&]() { ++post_calls; });

  // A successful solve invokes post_randomize() exactly once.
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(post_calls, 1);

  // Now make the constraints infeasible.
  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr eq_lo;
  eq_lo.kind = ConstraintKind::kEqual;
  eq_lo.var_name = "x";
  eq_lo.lo = 10;
  block.constraints.push_back(eq_lo);
  ConstraintExpr eq_hi;
  eq_hi.kind = ConstraintKind::kEqual;
  eq_hi.var_name = "x";
  eq_hi.lo = 20;
  block.constraints.push_back(eq_hi);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
  // The failing randomize() did not call post_randomize(): still one call.
  EXPECT_EQ(post_calls, 1);
}

// 18.6.3: randomize() implements object random stability — an object's random
// values are reproducible from its seed. Two solvers seeded identically and set
// up identically produce the same value across a sequence of solves, while a
// solver seeded differently is not bound to the same sequence. This is the
// per-object RNG that 18.13.3's srandom() seeds.
TEST(BehaviorOfRandomizationMethods, ObjectRandomStabilityIsSeedDetermined) {
  auto make_solver = [](uint32_t seed) {
    auto s = std::make_unique<ConstraintSolver>(seed);
    RandVariable v;
    v.name = "x";
    v.min_val = 0;
    v.max_val = 1000000;
    s->AddVariable(v);
    return s;
  };

  auto a = make_solver(123);
  auto b = make_solver(123);
  auto c = make_solver(456);

  bool c_differs = false;
  for (int i = 0; i < 4; ++i) {
    ASSERT_TRUE(a->Solve());
    ASSERT_TRUE(b->Solve());
    ASSERT_TRUE(c->Solve());
    // Same seed, same setup: the same sequence of random values.
    EXPECT_EQ(a->GetValue("x"), b->GetValue("x"));
    if (c->GetValue("x") != a->GetValue("x")) c_differs = true;
  }
  // A different seed yields a different object RNG, so its values are not tied
  // to the first object's sequence.
  EXPECT_TRUE(c_differs);
}

// 18.6.3 (edge of B1 + B2): the shared cell of a static random variable is only
// updated by a successful randomize(). When one instance commits a value and a
// later randomize() on another instance fails, the failing call leaves the
// shared value at the one the successful call published — it does not change
// the static variable in any instance, since the variables retain their
// previous values on failure.
TEST(BehaviorOfRandomizationMethods,
     FailedRandomizeLeavesSharedStaticUnchanged) {
  auto shared = std::make_shared<int64_t>(0);

  auto make_static = [&]() {
    RandVariable v;
    v.name = "x";
    v.min_val = 0;
    v.max_val = 1000;
    v.is_static = true;
    v.shared_value = shared;
    return v;
  };

  ConstraintSolver inst_a(5);
  ConstraintSolver inst_b(9);
  inst_a.AddVariable(make_static());
  inst_b.AddVariable(make_static());

  // Instance A pins the static variable to 7 and commits it for all instances.
  ConstraintBlock pin_a;
  pin_a.name = "ca";
  ConstraintExpr eq_a;
  eq_a.kind = ConstraintKind::kEqual;
  eq_a.var_name = "x";
  eq_a.lo = 7;
  pin_a.constraints.push_back(eq_a);
  inst_a.AddConstraintBlock(pin_a);

  ASSERT_TRUE(inst_a.Solve());
  ASSERT_EQ(inst_a.GetValue("x"), 7);
  ASSERT_EQ(inst_b.GetValue("x"), 7);

  // Instance B has an infeasible constraint set (pinned to two values at once),
  // so its randomize() fails.
  ConstraintBlock bad_b;
  bad_b.name = "cb";
  ConstraintExpr eq_lo;
  eq_lo.kind = ConstraintKind::kEqual;
  eq_lo.var_name = "x";
  eq_lo.lo = 1;
  bad_b.constraints.push_back(eq_lo);
  ConstraintExpr eq_hi;
  eq_hi.kind = ConstraintKind::kEqual;
  eq_hi.var_name = "x";
  eq_hi.lo = 2;
  bad_b.constraints.push_back(eq_hi);
  inst_b.AddConstraintBlock(bad_b);

  EXPECT_FALSE(inst_b.Solve());
  // The failed call published nothing: every instance still sees A's value.
  EXPECT_EQ(inst_a.GetValue("x"), 7);
  EXPECT_EQ(inst_b.GetValue("x"), 7);
}

// 18.6.3 (edge of B2): a failed randomize() restores every random variable, not
// only the one the infeasible constraint names. With two variables solved
// successfully and a later solve made infeasible through one of them, both keep
// the values from the successful solve rather than the partial draws the failed
// search attempted.
TEST(BehaviorOfRandomizationMethods, FailedRandomizeRetainsAllPreviousValues) {
  ConstraintSolver solver(13);
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

  ASSERT_TRUE(solver.Solve());
  const int64_t prev_a = solver.GetValue("a");
  const int64_t prev_b = solver.GetValue("b");

  // Make 'a' infeasible (pinned to two values); 'b' is left unconstrained.
  ConstraintBlock block;
  block.name = "c";
  ConstraintExpr eq_lo;
  eq_lo.kind = ConstraintKind::kEqual;
  eq_lo.var_name = "a";
  eq_lo.lo = 10;
  block.constraints.push_back(eq_lo);
  ConstraintExpr eq_hi;
  eq_hi.kind = ConstraintKind::kEqual;
  eq_hi.var_name = "a";
  eq_hi.lo = 20;
  block.constraints.push_back(eq_hi);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
  // Both variables retain the values from the last successful randomize().
  EXPECT_EQ(solver.GetValue("a"), prev_a);
  EXPECT_EQ(solver.GetValue("b"), prev_b);
}

}  // namespace
