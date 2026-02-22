// §18.6: Randomization methods

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
// §18.7: randomize() return value
// =============================================================================
TEST(Constraint, RandomizeSuccess) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);
  EXPECT_TRUE(solver.Solve());
}

TEST(Constraint, RandomizeFailureContradiction) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_contra";
  ConstraintExpr c1;
  c1.kind = ConstraintKind::kEqual;
  c1.var_name = "x";
  c1.lo = 50;
  block.constraints.push_back(c1);
  ConstraintExpr c2;
  c2.kind = ConstraintKind::kEqual;
  c2.var_name = "x";
  c2.lo = 60;
  block.constraints.push_back(c2);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
}

// =============================================================================
// §18.7.2: Pre/post randomize hooks
// =============================================================================
TEST(Constraint, PreRandomizeHook) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  bool pre_called = false;
  solver.SetPreRandomize([&pre_called]() { pre_called = true; });

  ASSERT_TRUE(solver.Solve());
  EXPECT_TRUE(pre_called);
}

TEST(Constraint, PostRandomizeHook) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  bool post_called = false;
  solver.SetPostRandomize([&post_called]() { post_called = true; });

  ASSERT_TRUE(solver.Solve());
  EXPECT_TRUE(post_called);
}

TEST(Constraint, PrePostRandomizeOrder) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  std::vector<std::string> order;
  solver.SetPreRandomize([&order]() { order.push_back("pre"); });
  solver.SetPostRandomize([&order]() { order.push_back("post"); });

  ASSERT_TRUE(solver.Solve());
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre");
  EXPECT_EQ(order[1], "post");
}

// =============================================================================
// Values map access
// =============================================================================
TEST(Constraint, GetValuesMap) {
  ConstraintSolver solver(42);
  RandVariable va;
  va.name = "a";
  va.min_val = 0;
  va.max_val = 10;
  solver.AddVariable(va);

  RandVariable vb;
  vb.name = "b";
  vb.min_val = 0;
  vb.max_val = 10;
  solver.AddVariable(vb);

  ASSERT_TRUE(solver.Solve());
  const auto &vals = solver.GetValues();
  EXPECT_EQ(vals.size(), 2u);
  EXPECT_TRUE(vals.count("a"));
  EXPECT_TRUE(vals.count("b"));
}

// =============================================================================
// Post-randomize not called on failure
// =============================================================================
TEST(Constraint, PostRandomizeFailureNoCallback) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_contra";
  ConstraintExpr c1;
  c1.kind = ConstraintKind::kEqual;
  c1.var_name = "x";
  c1.lo = 10;
  block.constraints.push_back(c1);
  ConstraintExpr c2;
  c2.kind = ConstraintKind::kEqual;
  c2.var_name = "x";
  c2.lo = 20;
  block.constraints.push_back(c2);
  solver.AddConstraintBlock(block);

  bool post_called = false;
  solver.SetPostRandomize([&post_called]() { post_called = true; });

  EXPECT_FALSE(solver.Solve());
  EXPECT_FALSE(post_called);
}

}  // namespace
