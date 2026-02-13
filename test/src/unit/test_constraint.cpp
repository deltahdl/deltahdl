#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulation/constraint_solver.h"

using namespace delta;

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

// =============================================================================
// §18.5.1-18.5.2: Simple constraint blocks
// =============================================================================

TEST(Constraint, SimpleRangeConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_range";
  ConstraintExpr c;
  c.kind = ConstraintKind::kRange;
  c.var_name = "x";
  c.lo = 10;
  c.hi = 20;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_GE(val, 10);
  EXPECT_LE(val, 20);
}

TEST(Constraint, EqualityConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_eq";
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = "x";
  c.lo = 42;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 42);
}

TEST(Constraint, InequalityConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_gt";
  ConstraintExpr c;
  c.kind = ConstraintKind::kGreaterThan;
  c.var_name = "x";
  c.lo = 90;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GT(solver.GetValue("x"), 90);
}

// =============================================================================
// §18.5.3: Set membership (inside)
// =============================================================================

TEST(Constraint, InsideSetMembership) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "mode";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_inside";
  ConstraintExpr c;
  c.kind = ConstraintKind::kSetMembership;
  c.var_name = "mode";
  c.set_values = {1, 5, 10, 50};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("mode");
  EXPECT_TRUE(val == 1 || val == 5 || val == 10 || val == 50);
}

TEST(Constraint, InsideSetSingleValue) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_single";
  ConstraintExpr c;
  c.kind = ConstraintKind::kSetMembership;
  c.var_name = "x";
  c.set_values = {77};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 77);
}

// =============================================================================
// §18.5.4: Distribution constraints (dist)
// =============================================================================

TEST(Constraint, DistributionWeighted) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_dist";
  ConstraintExpr c;
  c.kind = ConstraintKind::kDist;
  c.var_name = "x";
  c.dist_weights = {{10, 1000}, {20, 1}};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  int count_10 = 0;
  for (int i = 0; i < 100; ++i) {
    ASSERT_TRUE(solver.Solve());
    if (solver.GetValue("x") == 10) ++count_10;
  }
  EXPECT_GT(count_10, 80);
}

TEST(Constraint, DistributionUniform) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_dist_uniform";
  ConstraintExpr c;
  c.kind = ConstraintKind::kDist;
  c.var_name = "x";
  c.dist_weights = {{1, 1}, {2, 1}, {3, 1}};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_TRUE(val >= 1 && val <= 3);
}

// =============================================================================
// §18.5.6: Implication constraints (if-else)
// =============================================================================

TEST(Constraint, ImplicationTrue) {
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

  ConstraintBlock b1;
  b1.name = "c_mode";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "mode";
  eq.lo = 1;
  b1.constraints.push_back(eq);
  solver.AddConstraintBlock(b1);

  ConstraintBlock b2;
  b2.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "mode";
  impl.cond_value = 1;
  ConstraintExpr sub;
  sub.kind = ConstraintKind::kRange;
  sub.var_name = "data";
  sub.lo = 10;
  sub.hi = 20;
  impl.sub_constraints.push_back(sub);
  b2.constraints.push_back(impl);
  solver.AddConstraintBlock(b2);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("mode"), 1);
  EXPECT_GE(solver.GetValue("data"), 10);
  EXPECT_LE(solver.GetValue("data"), 20);
}

TEST(Constraint, ImplicationFalseAntecedent) {
  ConstraintSolver solver(42);
  RandVariable vmode;
  vmode.name = "mode";
  vmode.min_val = 0;
  vmode.max_val = 255;
  solver.AddVariable(vmode);

  RandVariable vdata;
  vdata.name = "data";
  vdata.min_val = 0;
  vdata.max_val = 255;
  solver.AddVariable(vdata);

  ConstraintBlock b1;
  b1.name = "c_mode";
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "mode";
  eq.lo = 0;
  b1.constraints.push_back(eq);
  solver.AddConstraintBlock(b1);

  ConstraintBlock b2;
  b2.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "mode";
  impl.cond_value = 1;
  ConstraintExpr sub;
  sub.kind = ConstraintKind::kEqual;
  sub.var_name = "data";
  sub.lo = 99;
  impl.sub_constraints.push_back(sub);
  b2.constraints.push_back(impl);
  solver.AddConstraintBlock(b2);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("mode"), 0);
  EXPECT_GE(solver.GetValue("data"), 0);
  EXPECT_LE(solver.GetValue("data"), 255);
}

// =============================================================================
// §18.5.7: Iterative constraints (foreach)
// =============================================================================

TEST(Constraint, ForeachConstraint) {
  ConstraintSolver solver(42);
  for (int i = 0; i < 3; ++i) {
    RandVariable v;
    v.name = "arr_" + std::to_string(i);
    v.min_val = 0;
    v.max_val = 100;
    solver.AddVariable(v);
  }

  ConstraintBlock block;
  block.name = "c_foreach";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  for (int i = 0; i < 3; ++i) {
    ConstraintExpr sub;
    sub.kind = ConstraintKind::kRange;
    sub.var_name = "arr_" + std::to_string(i);
    sub.lo = 10;
    sub.hi = 50;
    fe.sub_constraints.push_back(sub);
  }
  block.constraints.push_back(fe);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  for (int i = 0; i < 3; ++i) {
    int64_t val = solver.GetValue("arr_" + std::to_string(i));
    EXPECT_GE(val, 10);
    EXPECT_LE(val, 50);
  }
}

// =============================================================================
// §18.5.5: Unique constraints
// =============================================================================

TEST(Constraint, UniqueConstraint) {
  ConstraintSolver solver(42);
  for (int i = 0; i < 3; ++i) {
    RandVariable v;
    v.name = "u" + std::to_string(i);
    v.min_val = 0;
    v.max_val = 100;
    solver.AddVariable(v);
  }

  ConstraintBlock block;
  block.name = "c_unique";
  ConstraintExpr uc;
  uc.kind = ConstraintKind::kUnique;
  uc.unique_vars = {"u0", "u1", "u2"};
  block.constraints.push_back(uc);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t v0 = solver.GetValue("u0");
  int64_t v1 = solver.GetValue("u1");
  int64_t v2 = solver.GetValue("u2");
  EXPECT_NE(v0, v1);
  EXPECT_NE(v1, v2);
  EXPECT_NE(v0, v2);
}

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
// §18.7.1: Inline constraints (randomize() with {})
// =============================================================================

TEST(Constraint, InlineConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintExpr inline_c;
  inline_c.kind = ConstraintKind::kEqual;
  inline_c.var_name = "x";
  inline_c.lo = 77;

  ASSERT_TRUE(solver.SolveWith({inline_c}));
  EXPECT_EQ(solver.GetValue("x"), 77);
}

TEST(Constraint, InlineConstraintWithBlock) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_block";
  ConstraintExpr bc;
  bc.kind = ConstraintKind::kGreaterEqual;
  bc.var_name = "x";
  bc.lo = 50;
  block.constraints.push_back(bc);
  solver.AddConstraintBlock(block);

  ConstraintExpr inline_c;
  inline_c.kind = ConstraintKind::kLessEqual;
  inline_c.var_name = "x";
  inline_c.lo = 60;

  ASSERT_TRUE(solver.SolveWith({inline_c}));
  int64_t val = solver.GetValue("x");
  EXPECT_GE(val, 50);
  EXPECT_LE(val, 60);
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
// §18.8: rand_mode() enable/disable
// =============================================================================

TEST(Constraint, RandModeDisable) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  EXPECT_TRUE(solver.GetRandMode("x"));
  solver.SetRandMode("x", false);
  EXPECT_FALSE(solver.GetRandMode("x"));

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 0);
}

TEST(Constraint, RandModeReEnable) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 1;
  v.max_val = 100;
  solver.AddVariable(v);

  solver.SetRandMode("x", false);
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 0);

  solver.SetRandMode("x", true);
  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 1);
  EXPECT_LE(solver.GetValue("x"), 100);
}

// =============================================================================
// §18.9: constraint_mode() enable/disable
// =============================================================================

TEST(Constraint, ConstraintModeDisable_ActiveSolve) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_tight";
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = "x";
  c.lo = 42;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 42);
}

TEST(Constraint, ConstraintModeDisable_DisabledSolve) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_tight";
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = "x";
  c.lo = 42;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  solver.SetConstraintMode("c_tight", false);
  EXPECT_FALSE(solver.GetConstraintMode("c_tight"));
  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 0);
  EXPECT_LE(solver.GetValue("x"), 1000);
}

TEST(Constraint, ConstraintModeReEnable) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_eq";
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = "x";
  c.lo = 77;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  solver.SetConstraintMode("c_eq", false);
  ASSERT_TRUE(solver.Solve());

  solver.SetConstraintMode("c_eq", true);
  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 77);
}

// =============================================================================
// §18.11: std::randomize() standalone function
// =============================================================================

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

// =============================================================================
// §18.17: randsequence (basic structure)
// =============================================================================

TEST(Constraint, RandsequenceBasicProduction) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "production";
  v.min_val = 0;
  v.max_val = 2;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_seq";
  ConstraintExpr c;
  c.kind = ConstraintKind::kDist;
  c.var_name = "production";
  c.dist_weights = {{0, 1}, {1, 1}, {2, 1}};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("production");
  EXPECT_GE(val, 0);
  EXPECT_LE(val, 2);
}

// =============================================================================
// §18.5.13: Soft constraints
// =============================================================================

TEST(Constraint, SoftConstraintYieldsToHard) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  // Soft: x == 50.
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

  // Hard: x == 30. This overrides soft.
  ConstraintBlock b_hard;
  b_hard.name = "c_hard";
  ConstraintExpr hc;
  hc.kind = ConstraintKind::kEqual;
  hc.var_name = "x";
  hc.lo = 30;
  b_hard.constraints.push_back(hc);
  solver.AddConstraintBlock(b_hard);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 30);
}

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

  // Soft alone: no crash, value is in valid range.
  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 0);
  EXPECT_LE(solver.GetValue("x"), 100);
}

// =============================================================================
// Constraint solver ordering
// =============================================================================

TEST(Constraint, SolverOrderingMultipleBlocks) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 1000;
  solver.AddVariable(v);

  ConstraintBlock b1;
  b1.name = "c1";
  ConstraintExpr c1;
  c1.kind = ConstraintKind::kGreaterEqual;
  c1.var_name = "x";
  c1.lo = 100;
  b1.constraints.push_back(c1);
  solver.AddConstraintBlock(b1);

  ConstraintBlock b2;
  b2.name = "c2";
  ConstraintExpr c2;
  c2.kind = ConstraintKind::kLessEqual;
  c2.var_name = "x";
  c2.lo = 200;
  b2.constraints.push_back(c2);
  solver.AddConstraintBlock(b2);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("x");
  EXPECT_GE(val, 100);
  EXPECT_LE(val, 200);
}

// =============================================================================
// §18.5: Custom constraint with callback
// =============================================================================

TEST(Constraint, CustomConstraintCallback) {
  ConstraintSolver solver(42);
  RandVariable va;
  va.name = "a";
  va.min_val = 0;
  va.max_val = 50;
  solver.AddVariable(va);

  RandVariable vb;
  vb.name = "b";
  vb.min_val = 0;
  vb.max_val = 50;
  solver.AddVariable(vb);

  ConstraintBlock block;
  block.name = "c_custom";
  ConstraintExpr c;
  c.kind = ConstraintKind::kCustom;
  c.eval_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    auto ita = vals.find("a");
    auto itb = vals.find("b");
    if (ita == vals.end() || itb == vals.end()) return true;
    return ita->second + itb->second <= 30;
  };
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_LE(solver.GetValue("a") + solver.GetValue("b"), 30);
}

// =============================================================================
// Not-equal constraint
// =============================================================================

TEST(Constraint, NotEqualConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 10;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_neq";
  ConstraintExpr c;
  c.kind = ConstraintKind::kNotEqual;
  c.var_name = "x";
  c.lo = 5;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_NE(solver.GetValue("x"), 5);
}

// =============================================================================
// Less-than constraint
// =============================================================================

TEST(Constraint, LessThanConstraint) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "x";
  v.min_val = 0;
  v.max_val = 100;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_lt";
  ConstraintExpr c;
  c.kind = ConstraintKind::kLessThan;
  c.var_name = "x";
  c.lo = 10;
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_LT(solver.GetValue("x"), 10);
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
  const auto& vals = solver.GetValues();
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
