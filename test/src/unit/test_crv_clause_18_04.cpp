// §18.4: Random variables

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
// §18.3: rand variable modifier
// =============================================================================
TEST(Constraint, RandVariableBasic) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.qualifier = RandQualifier::kRand;
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_GE(val, 0);
  EXPECT_LE(val, 100);
}

TEST(Constraint, RandVariableMultiple) {
  ConstraintSolver solver(42);
  for (const auto& name : {"a", "b", "c"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 0;
    v.max_val = 255;
    solver.AddVariable(v);
  }
  ASSERT_TRUE(solver.Solve());
  for (const auto& name : {"a", "b", "c"}) {
    int64_t val = solver.GetValue(name);
    EXPECT_GE(val, 0);
    EXPECT_LE(val, 255);
  }
}

// =============================================================================
// §18.4: randc cyclic random
// =============================================================================
TEST(Constraint, RandcCyclic) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.qualifier = RandQualifier::kRandc;
  v.min_val = 0;
  v.max_val = 3;
  solver.AddVariable(v);

  std::unordered_set<int64_t> seen;
  for (int i = 0; i < 4; ++i) {
    ASSERT_TRUE(solver.Solve());
    seen.insert(solver.GetValue("x"));
  }
  EXPECT_EQ(seen.size(), 4u);
}

TEST(Constraint, RandcCycleResets) {
  ConstraintSolver solver(123);
  RandVariable v;
  v.name = "y";
  v.qualifier = RandQualifier::kRandc;
  v.min_val = 0;
  v.max_val = 1;
  solver.AddVariable(v);

  std::unordered_set<int64_t> cycle1;
  for (int i = 0; i < 2; ++i) {
    ASSERT_TRUE(solver.Solve());
    cycle1.insert(solver.GetValue("y"));
  }
  EXPECT_EQ(cycle1.size(), 2u);

  std::unordered_set<int64_t> cycle2;
  for (int i = 0; i < 2; ++i) {
    ASSERT_TRUE(solver.Solve());
    cycle2.insert(solver.GetValue("y"));
  }
  EXPECT_EQ(cycle2.size(), 2u);
}

}  // namespace
