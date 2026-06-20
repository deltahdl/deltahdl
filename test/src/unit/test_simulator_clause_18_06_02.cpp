#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// 18.6.2: when randomize() runs, it first invokes pre_randomize() — before any
// new random values are computed — and, after the new values are computed and
// assigned, invokes post_randomize(). Observed through the solver's
// pre/post hooks: at the moment pre_randomize() fires no value has been
// produced yet, and at the moment post_randomize() fires the value is present.
TEST(PrePostRandomize, PreBeforeComputePostAfterCompute) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  size_t values_at_pre = 999;
  size_t values_at_post = 999;
  solver.SetPreRandomize([&]() { values_at_pre = solver.GetValues().size(); });
  solver.SetPostRandomize(
      [&]() { values_at_post = solver.GetValues().size(); });

  ASSERT_TRUE(solver.Solve());

  // pre_randomize() ran before the random value for x existed.
  EXPECT_EQ(values_at_pre, 0u);
  // post_randomize() ran after the value was computed and assigned.
  EXPECT_EQ(values_at_post, 1u);
}

// 18.6.2: every class contains pre_randomize() and post_randomize() methods.
// A class that does not override them has built-in versions whose processing
// is empty, so randomization proceeds and produces a value exactly as if they
// were absent. The solver models "not overridden" as having no pre/post hook
// registered; with neither hook set, Solve() still randomizes successfully and
// the default built-ins contribute no processing of their own.
TEST(PrePostRandomize, DefaultBuiltinsAreNoOpsWhenNotOverridden) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  // No SetPreRandomize/SetPostRandomize: the default built-in methods apply.
  ASSERT_TRUE(solver.Solve());

  // The random variable was still computed and assigned a value in range.
  ASSERT_EQ(solver.GetValues().size(), 1u);
  const int64_t kX = solver.GetValues().at("x");
  EXPECT_GE(kX, 0);
  EXPECT_LE(kX, 100);
}

// 18.6.2: a single randomize() first invokes pre_randomize() and then, after
// the values are computed, invokes post_randomize(). Beyond the compute
// boundary, this fixes both the relative order of the two methods and their
// cardinality: across one Solve() each hook fires exactly once, with
// pre_randomize() strictly preceding post_randomize(). Recording an ordered
// log from the solver's pre/post hook sites observes that sequence directly.
TEST(PrePostRandomize, PreThenPostInvokedExactlyOnceInOrder) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  std::vector<std::string> events;
  solver.SetPreRandomize([&]() { events.push_back("pre"); });
  solver.SetPostRandomize([&]() { events.push_back("post"); });

  ASSERT_TRUE(solver.Solve());

  // pre fired once, then post fired once — no extra or missing invocations.
  const std::vector<std::string> kExpected = {"pre", "post"};
  EXPECT_EQ(events, kExpected);
}

}  // namespace
