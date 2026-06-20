#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "helpers_constraint_rel.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// 18.11: when randomize() is called with arguments, those arguments designate
// the complete set of random variables; every other variable in the object is
// considered a state variable. Here only "x" is named, so "y" and "z" are held
// at their current values while "x" is solved against them.
TEST(InlineRandomControl, ArgListDesignatesCompleteRandomSet) {
  ConstraintSolver solver(42);

  for (const char* name : {"x", "y", "z"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 0;
    v.max_val = 10;
    solver.AddVariable(v);
  }

  // Give the would-be state variables known current values.
  solver.SetValue("y", 4);
  solver.SetValue("z", 7);

  AddXEqualsYPlusOneConstraint(solver);

  // randomize(x): only x is random; y and z are state variables.
  solver.ApplyInlineRandomList({"x"});

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("y"), 4);  // state variable, unchanged
  EXPECT_EQ(solver.GetValue("z"), 7);  // state variable, unchanged
  EXPECT_EQ(solver.GetValue("x"), 5);  // randomized against y's fixed value
}

// 18.11: the mechanism is conceptually equivalent to a set of rand_mode() calls
// that enable the named variables and disable the rest. The resulting active
// states are observable exactly as rand_mode() would leave them.
TEST(InlineRandomControl, EquivalentToRandModeToggles) {
  ConstraintSolver solver(42);

  for (const char* name : {"a", "b", "c"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 1;
    v.max_val = 100;
    solver.AddVariable(v);
  }

  solver.ApplyInlineRandomList({"a", "c"});

  EXPECT_TRUE(solver.GetRandMode("a"));   // named -> active
  EXPECT_FALSE(solver.GetRandMode("b"));  // unnamed -> state variable
  EXPECT_TRUE(solver.GetRandMode("c"));   // named -> active

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("a"), 1);
  EXPECT_GE(solver.GetValue("c"), 1);
  EXPECT_EQ(solver.GetValue("b"), 0);  // inactive variable is not randomized
}

// 18.11: calling randomize() with arguments allows changing the random mode of
// any class property, even one not declared rand or randc. A property modeled
// with no random qualifier becomes active and is randomized when named, while a
// declared rand variable that is not named becomes a state variable.
TEST(InlineRandomControl, NamesNonRandPropertyAndDeactivatesUnnamed) {
  ConstraintSolver solver(42);

  RandVariable p;  // a property not declared rand/randc
  p.name = "p";
  p.qualifier = RandQualifier::kNone;
  p.min_val = 5;
  p.max_val = 9;
  solver.AddVariable(p);

  RandVariable q;  // a declared rand variable, left unnamed
  q.name = "q";
  q.qualifier = RandQualifier::kRand;
  q.min_val = 1;
  q.max_val = 100;
  solver.AddVariable(q);

  solver.ApplyInlineRandomList({"p"});

  EXPECT_TRUE(solver.GetRandMode("p"));   // non-rand property made active
  EXPECT_FALSE(solver.GetRandMode("q"));  // unnamed rand variable made state

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("p"), 5);  // randomized despite not being rand
  EXPECT_LE(solver.GetValue("p"), 9);
  EXPECT_EQ(solver.GetValue("q"), 0);  // state variable, not randomized
}

// 18.11: the inline control list applies to a single randomize() call, so each
// call re-designates the active random set from scratch. A later list naming a
// different variable makes that variable random and returns the previously
// named one to state-variable status.
TEST(InlineRandomControl, ReapplyingInlineListRedesignatesActiveSet) {
  ConstraintSolver solver(42);

  for (const char* name : {"a", "b"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 1;
    v.max_val = 100;
    solver.AddVariable(v);
  }

  solver.ApplyInlineRandomList({"a"});
  EXPECT_TRUE(solver.GetRandMode("a"));
  EXPECT_FALSE(solver.GetRandMode("b"));

  // A second call names a different variable: the active set is replaced, not
  // accumulated.
  solver.ApplyInlineRandomList({"b"});
  EXPECT_FALSE(solver.GetRandMode("a"));
  EXPECT_TRUE(solver.GetRandMode("b"));

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("a"), 0);  // back to state variable
  EXPECT_GE(solver.GetValue("b"), 1);  // now randomized
}

// 18.11: the mechanism does not affect the cyclical random mode; it cannot
// change a cyclical random variable into a noncyclical one. A randc variable
// named in the inline list keeps cycling through its full set of distinct
// values before any value repeats.
TEST(InlineRandomControl, NamedRandcKeepsCyclicalMode) {
  ConstraintSolver solver(7);

  RandVariable c;
  c.name = "c";
  c.qualifier = RandQualifier::kRandc;
  c.min_val = 0;
  c.max_val = 3;
  solver.AddVariable(c);

  solver.ApplyInlineRandomList({"c"});

  std::vector<int64_t> seen;
  for (int i = 0; i < 4; ++i) {
    ASSERT_TRUE(solver.Solve());
    seen.push_back(solver.GetValue("c"));
  }
  std::sort(seen.begin(), seen.end());
  // A noncyclical variable could repeat; a still-cyclical randc draws each of
  // 0..3 exactly once across the permutation.
  EXPECT_EQ(seen, (std::vector<int64_t>{0, 1, 2, 3}));
}

// 18.11: the mechanism cannot change a nonrandom variable into a cyclical
// (randc) one. A property with no random qualifier that is named in the inline
// list is randomized as a noncyclical variable, so over a small domain it does
// repeat values rather than exhausting a permutation the way randc would.
TEST(InlineRandomControl, NamedNonRandIsNotPromotedToCyclical) {
  ConstraintSolver solver(1);

  RandVariable p;
  p.name = "p";
  p.qualifier = RandQualifier::kNone;
  p.min_val = 0;
  p.max_val = 1;
  solver.AddVariable(p);

  solver.ApplyInlineRandomList({"p"});

  bool consecutive_repeat = false;
  int64_t prev = -1;
  for (int i = 0; i < 40; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t v = solver.GetValue("p");
    if (v == prev) consecutive_repeat = true;
    prev = v;
  }
  // randc over {0,1} would strictly alternate (never two equal in a row); a
  // noncyclical draw repeats, confirming the variable was not promoted.
  EXPECT_TRUE(consecutive_repeat);
}

}  // namespace
