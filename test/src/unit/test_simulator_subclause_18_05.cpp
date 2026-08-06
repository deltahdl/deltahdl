#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "helpers_scheduler.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

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

// 18.5: "The values of random variables are determined using constraint
// expressions that are declared using constraint blocks." A relation between
// two random variables is such an expression, so it has to hold of the values
// randomize() commits. Neither side is a bound the other can be folded against
// before the solve: both are still to be drawn, and reading one of them early
// yields the value it happens to be holding rather than the one it will take.
//
// Stated from source rather than by building solver variables, because what
// goes wrong lives in the translation from the constraint expression to the
// solver, not in the solver's own handling of a bound. Two-bit variables keep
// it cheap -- a quarter of the sixteen combinations satisfy the equality, and
// six satisfy the ordering -- so a solve that honors the relation converges at
// once, while one that folded it would satisfy it only by coincidence and
// report success regardless.
TEST(Constraint, EqualityBetweenTwoRandomVariablesHoldsFromSource) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] a;\n"
      "  rand bit [1:0] b;\n"
      "  constraint c { a == b; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i;\n"
      "    C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 40; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.a != o.b) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

// 18.5, the ordering form of the same rule: `a < b` relates two random
// variables and holds of every committed pair.
TEST(Constraint, OrderingBetweenTwoRandomVariablesHoldsFromSource) {
  const char* src =
      "class C;\n"
      "  rand bit [1:0] a;\n"
      "  rand bit [1:0] b;\n"
      "  constraint c { a < b; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    int i;\n"
      "    C o = new;\n"
      "    good = 1;\n"
      "    for (i = 0; i < 40; i = i + 1) begin\n"
      "      if (o.randomize() == 0) good = 0;\n"
      "      if (o.a >= o.b) good = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

}  // namespace
