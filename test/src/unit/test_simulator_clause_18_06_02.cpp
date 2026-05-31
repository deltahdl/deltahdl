#include <gtest/gtest.h>

#include <cstddef>

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
  solver.SetPreRandomize(
      [&]() { values_at_pre = solver.GetValues().size(); });
  solver.SetPostRandomize(
      [&]() { values_at_post = solver.GetValues().size(); });

  ASSERT_TRUE(solver.Solve());

  // pre_randomize() ran before the random value for x existed.
  EXPECT_EQ(values_at_pre, 0u);
  // post_randomize() ran after the value was computed and assigned.
  EXPECT_EQ(values_at_post, 1u);
}

}
