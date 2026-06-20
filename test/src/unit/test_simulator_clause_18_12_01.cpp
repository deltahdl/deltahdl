#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// Build a custom relation over two named integral variables, supplied to a
// std::randomize() with block as one inline constraint. The relation is only
// enforced once both operands are present in the solved-value map.
ConstraintExpr Relation(std::function<bool(int64_t, int64_t)> rel,
                        std::string lhs, std::string rhs) {
  ConstraintExpr c;
  c.kind = ConstraintKind::kCustom;
  c.eval_fn = [rel = std::move(rel), lhs = std::move(lhs),
               rhs = std::move(rhs)](
                  const std::unordered_map<std::string, int64_t>& vals) {
    auto il = vals.find(lhs);
    auto ir = vals.find(rhs);
    if (il == vals.end() || ir == vals.end()) return true;
    return rel(il->second, ir->second);
  };
  return c;
}

// 18.12.1: with std::randomize() with, the arguments to the scope randomize
// function become the random variables and every other variable is a state
// variable. This mirrors the clause's example std::randomize(a, b) with
// { a < b; a + b < length; }: a and b are named, so they are randomized, while
// the task argument length is named in no list and is held at its current
// value as a state variable that the constraint reads as a constant.
TEST(ScopeRandomizeWith, NamedArgumentsRandomNonArgumentsAreState) {
  ConstraintSolver solver(42);
  for (const char* name : {"a", "b", "length"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 0;
    v.max_val = 20;
    solver.AddVariable(v);
  }
  // The task argument is a state variable with a known current value.
  solver.SetValue("length", 15);

  // randomize(a, b): only a and b are random; length stays a state variable.
  solver.ApplyInlineRandomList({"a", "b"});

  // with { a < b; a + b < length; }
  std::vector<ConstraintExpr> with = {
      Relation([](int64_t a, int64_t b) { return a < b; }, "a", "b"),
      Relation([](int64_t a, int64_t b) { return a + b < 15; }, "a", "b")};

  ASSERT_TRUE(solver.SolveWith(with));
  EXPECT_LT(solver.GetValue("a"), solver.GetValue("b"));
  EXPECT_LT(solver.GetValue("a") + solver.GetValue("b"), 15);
  EXPECT_EQ(solver.GetValue("length"), 15);  // state variable, never randomized
}

// 18.12.1: a variable that is not one of the scope randomize arguments is a
// state variable, so the constraint sees its current value as a constant. The
// clause's second call, std::randomize(a, b) with { b - a > length; },
// constrains the named a and b relative to that fixed length. Solving the same
// constraint against two different current values of length yields draws that
// respect each one, confirming the value was read from the state variable
// rather than chosen by the solver.
TEST(ScopeRandomizeWith, StateVariableValueConstrainsTheDraw) {
  ConstraintSolver solver(7);
  for (const char* name : {"a", "b", "length"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 0;
    v.max_val = 50;
    solver.AddVariable(v);
  }
  solver.ApplyInlineRandomList({"a", "b"});

  // The constraint compares against length's seeded value, so rebuild it per
  // length to mirror the same with-block evaluated under each state value.
  auto with_for = [](int64_t length) {
    return std::vector<ConstraintExpr>{Relation(
        [length](int64_t a, int64_t b) { return b - a > length; }, "a", "b")};
  };

  solver.SetValue("length", 10);
  ASSERT_TRUE(solver.SolveWith(with_for(10)));
  EXPECT_GT(solver.GetValue("b") - solver.GetValue("a"), 10);
  EXPECT_EQ(solver.GetValue("length"), 10);

  solver.SetValue("length", 30);
  ASSERT_TRUE(solver.SolveWith(with_for(30)));
  EXPECT_GT(solver.GetValue("b") - solver.GetValue("a"), 30);
  EXPECT_EQ(solver.GetValue("length"), 30);
}

// 18.12.1: the arguments to the scope randomize function are the complete set
// of random variables; a local scope variable left out of the argument list is
// a state variable and keeps its current value across the call. Here only a and
// b are named, so the unnamed c is not randomized even though it is a known
// local variable, exactly as std::randomize(a, b) leaves c untouched.
TEST(ScopeRandomizeWith, UnnamedLocalVariableKeepsItsValue) {
  ConstraintSolver solver(99);
  for (const char* name : {"a", "b", "c"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 1;
    v.max_val = 30;
    solver.AddVariable(v);
  }
  solver.SetValue("c", 8);

  solver.ApplyInlineRandomList({"a", "b"});

  std::vector<ConstraintExpr> with = {
      Relation([](int64_t a, int64_t b) { return a < b; }, "a", "b")};

  ASSERT_TRUE(solver.SolveWith(with));
  EXPECT_LT(solver.GetValue("a"), solver.GetValue("b"));
  EXPECT_EQ(solver.GetValue("c"), 8);  // not an argument, so a state variable
}

// 18.12.1: every argument to the scope randomize function becomes a random
// variable, whether or not the with block constrains it. The clause's first
// call, std::randomize(a, b, c) with { a < b; a + b < length; }, names c even
// though no constraint mentions it, so c is still randomized. Here c carries a
// domain that excludes the default value a state variable would hold, so seeing
// c land inside that domain confirms it was drawn as a random variable rather
// than left untouched as a state variable.
TEST(ScopeRandomizeWith, NamedArgumentWithoutConstraintIsStillRandomized) {
  ConstraintSolver solver(123);

  RandVariable a;
  a.name = "a";
  a.min_val = 0;
  a.max_val = 20;
  solver.AddVariable(a);
  RandVariable b;
  b.name = "b";
  b.min_val = 0;
  b.max_val = 20;
  solver.AddVariable(b);
  RandVariable c;  // named, but constrained by nothing
  c.name = "c";
  c.min_val = 5;
  c.max_val = 9;
  solver.AddVariable(c);

  // randomize(a, b, c): all three are random variables; only a and b appear in
  // the with block.
  solver.ApplyInlineRandomList({"a", "b", "c"});

  std::vector<ConstraintExpr> with = {
      Relation([](int64_t a, int64_t b) { return a < b; }, "a", "b")};

  ASSERT_TRUE(solver.SolveWith(with));
  EXPECT_LT(solver.GetValue("a"), solver.GetValue("b"));
  // c was drawn into its own domain, so it is a random variable, not a state
  // variable holding its default (0, which lies outside [5, 9]).
  EXPECT_GE(solver.GetValue("c"), 5);
  EXPECT_LE(solver.GetValue("c"), 9);
}

// 18.12.1: because a non-argument variable is a state variable read as a fixed
// constant, its current value can leave the with constraint over the random
// arguments with no solution, in which case the scope randomize fails. Here the
// state variable length holds a value larger than any achievable difference of
// the named a and b, so b - a > length cannot be met and the call returns
// false.
TEST(ScopeRandomizeWith, UnsatisfiableAgainstStateValueFails) {
  ConstraintSolver solver(55);
  for (const char* name : {"a", "b", "length"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 0;
    v.max_val = 10;
    solver.AddVariable(v);
  }
  // No pair drawn from [0, 10] can differ by more than 10.
  solver.SetValue("length", 100);
  solver.ApplyInlineRandomList({"a", "b"});

  // with { b - a > length; } — length is read straight from the solved-value
  // map, where production has seeded it as the state variable's current value.
  ConstraintExpr c;
  c.kind = ConstraintKind::kCustom;
  c.eval_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    auto a = vals.find("a");
    auto b = vals.find("b");
    auto len = vals.find("length");
    if (a == vals.end() || b == vals.end() || len == vals.end()) return true;
    return b->second - a->second > len->second;
  };

  // The state variable's value of 100 is read as a constant during the solve,
  // so no draw of a and b can satisfy the with constraint and the call fails.
  EXPECT_FALSE(solver.SolveWith({c}));
}

// 18.12.1: a fresh argument list re-designates which local scope variables are
// random for that call. After a first std::randomize(a, b) draws a and b, a
// later std::randomize(a) with { ... } makes a the only random variable and
// returns b to state-variable status, so b is held at the value the first call
// gave it and read as a constant by the new constraint.
TEST(ScopeRandomizeWith, LaterCallRedesignatesRandomAndStateVariables) {
  ConstraintSolver solver(3);
  for (const char* name : {"a", "b"}) {
    RandVariable v;
    v.name = name;
    v.min_val = 0;
    v.max_val = 40;
    solver.AddVariable(v);
  }

  // First call: both a and b are random.
  solver.ApplyInlineRandomList({"a", "b"});
  ASSERT_TRUE(solver.SolveWith(
      {Relation([](int64_t a, int64_t b) { return a < b; }, "a", "b")}));
  const int64_t b_after_first = solver.GetValue("b");

  // Carry b's drawn value forward as its current value, then re-designate: now
  // only a is random and b is a state variable.
  solver.SetValue("b", b_after_first);
  solver.ApplyInlineRandomList({"a"});
  ASSERT_TRUE(solver.SolveWith({Relation(
      [b_after_first](int64_t a, int64_t) { return a > b_after_first / 2; },
      "a", "b")}));

  EXPECT_GT(solver.GetValue("a"), b_after_first / 2);
  EXPECT_EQ(solver.GetValue("b"), b_after_first);  // held as a state variable
}

}  // namespace
