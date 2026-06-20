#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_map>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// Builds the custom constraint left_v <= v used by every test in this file.
ConstraintExpr MakeLeftLeConstraint() {
  ConstraintExpr left_le;
  left_le.kind = ConstraintKind::kCustom;
  left_le.eval_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    auto v = vals.find("v");
    auto l = vals.find("left_v");
    if (v == vals.end() || l == vals.end()) return true;
    return l->second <= v->second;
  };
  return left_le;
}

// Builds a "heapcond" constraint block holding only the left_v <= v constraint,
// the shared global-constraint setup for the inactive-member tests.
ConstraintBlock MakeHeapCondLeftLe() {
  ConstraintBlock heapcond;
  heapcond.name = "heapcond";
  heapcond.constraints.push_back(MakeLeftLeConstraint());
  return heapcond;
}

// Adds a [min, max] random variable to the solver.
void AddRangeVariable(ConstraintSolver& solver, const std::string& name,
                      int64_t min_val, int64_t max_val) {
  RandVariable var;
  var.name = name;
  var.min_val = min_val;
  var.max_val = max_val;
  solver.AddVariable(var);
}

// Holds v at a fixed current value as an inactive state constant.
void HoldVAsStateConstant(ConstraintSolver& solver, int64_t value) {
  solver.SetValue("v", value);
  solver.SetRandMode("v", false);
}

// 18.5.8: when an object member is declared rand, its random variables and
// constraints are randomized simultaneously with the enclosing object's
// variables and constraints. A constraint relating random variables that come
// from different objects is a global constraint. Modeling the ordered-tree
// example, the heap node value v and its two subtree values are all active
// random variables solved together under the global constraints
// left.v <= v and right.v > v.
TEST(GlobalConstraint, ActiveVariablesSolvedSimultaneously) {
  ConstraintSolver solver(42);

  for (const char* name : {"v", "left_v", "right_v"}) {
    AddRangeVariable(solver, name, 0, 100);
  }

  ConstraintBlock heapcond = MakeHeapCondLeftLe();

  ConstraintExpr right_gt;
  right_gt.kind = ConstraintKind::kCustom;
  right_gt.eval_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    auto v = vals.find("v");
    auto r = vals.find("right_v");
    if (v == vals.end() || r == vals.end()) return true;
    return r->second > v->second;
  };
  heapcond.constraints.push_back(right_gt);

  solver.AddConstraintBlock(heapcond);

  ASSERT_TRUE(solver.Solve());
  EXPECT_LE(solver.GetValue("left_v"), solver.GetValue("v"));
  EXPECT_GT(solver.GetValue("right_v"), solver.GetValue("v"));
}

// 18.5.8: the active random variables are the ones randomized; every other
// variable reference is treated as a state variable whose current value is
// used as a constant. The active set is exactly the set of variables left
// active by rand_mode() (18.8). Here the heap value v is made inactive with a
// fixed current value, so the global constraint relating the still-active
// subtree value to v is solved against that constant rather than randomizing v.
TEST(GlobalConstraint, InactiveMemberIsStateConstantInGlobalConstraint) {
  ConstraintSolver solver(42);

  AddRangeVariable(solver, "v", 0, 100);
  AddRangeVariable(solver, "left_v", 0, 100);

  // v is not an active random variable: it holds its current value as a state
  // constant while left_v is randomized against it.
  HoldVAsStateConstant(solver, 8);

  solver.AddConstraintBlock(MakeHeapCondLeftLe());

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("v"), 8);
  EXPECT_LE(solver.GetValue("left_v"), 8);
}

// 18.5.8: because an inactive variable contributes its current value as a fixed
// constant rather than being randomized, a global constraint relating an active
// variable to it can become unsatisfiable. Here v is held at 0 while left_v can
// only take values in [5, 10], so left_v <= v has no solution and randomization
// fails — confirming the held value is a binding constant, not an ignored term.
TEST(GlobalConstraint,
     InactiveStateConstantCanMakeGlobalConstraintUnsatisfiable) {
  ConstraintSolver solver(42);

  AddRangeVariable(solver, "v", 0, 100);
  AddRangeVariable(solver, "left_v", 5, 10);

  HoldVAsStateConstant(solver, 0);

  solver.AddConstraintBlock(MakeHeapCondLeftLe());

  EXPECT_FALSE(solver.Solve());
}

}  // namespace
