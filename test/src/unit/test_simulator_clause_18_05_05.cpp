#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

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

// Helper: a variable pinned to a single value lets a test fix the truth of an
// antecedent or the satisfiability of a consequent deterministically.
RandVariable Pinned(const std::string& name, int64_t value) {
  RandVariable v;
  v.name = name;
  v.min_val = value;
  v.max_val = value;
  return v;
}

// 18.5.5: when the antecedent of "a -> b" is true, every constraint in the
// consequent shall be satisfied. With a pinned to 0 the antecedent (a == 0)
// always holds, so the solved value of b must obey the consequent b == 1.
TEST(ConstraintImplication, ConsequentSatisfiedWhenAntecedentTrue) {
  ConstraintSolver solver(7);
  solver.AddVariable(Pinned("a", 0));
  RandVariable b;
  b.name = "b";
  b.min_val = 0;
  b.max_val = 1;
  solver.AddVariable(b);

  ConstraintBlock block;
  block.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "a";
  impl.cond_value = 0;
  ConstraintExpr cons;
  cons.kind = ConstraintKind::kEqual;
  cons.var_name = "b";
  cons.lo = 1;
  impl.sub_constraints.push_back(cons);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("b"), 1);
}

// 18.5.5: if the antecedent is false the generated values are unconstrained,
// i.e. the consequent imposes nothing. Here a is pinned to 1 so (a == 0) is
// false; b is pinned to 0, which would violate the consequent b == 1 were it
// enforced. The solve must still succeed and leave b at 0.
TEST(ConstraintImplication, ConsequentIgnoredWhenAntecedentFalse) {
  ConstraintSolver solver(7);
  solver.AddVariable(Pinned("a", 1));
  solver.AddVariable(Pinned("b", 0));

  ConstraintBlock block;
  block.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "a";
  impl.cond_value = 0;
  ConstraintExpr cons;
  cons.kind = ConstraintKind::kEqual;
  cons.var_name = "b";
  cons.lo = 1;
  impl.sub_constraints.push_back(cons);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("b"), 0);
}

// 18.5.5: a -> b is Boolean-equivalent to (!a || b), and the two sides are
// interdependent. Pinning b to 0 makes the consequent b == 1 unsatisfiable, so
// the only way to satisfy the implication is for the antecedent to be false.
// The solver must therefore drive a away from 0 even though a is otherwise
// free to range over {0, 1}. This exercises the contrapositive direction.
TEST(ConstraintImplication, AntecedentConstrainedByUnsatisfiableConsequent) {
  ConstraintSolver solver(7);
  RandVariable a;
  a.name = "a";
  a.min_val = 0;
  a.max_val = 1;
  solver.AddVariable(a);
  solver.AddVariable(Pinned("b", 0));

  ConstraintBlock block;
  block.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "a";
  impl.cond_value = 0;
  ConstraintExpr cons;
  cons.kind = ConstraintKind::kEqual;
  cons.var_name = "b";
  cons.lo = 1;
  impl.sub_constraints.push_back(cons);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("a"), 1);
}

// 18.5.5: the constraint_set may be any valid constraint, not only an equality.
// Here the consequent is a range constraint, and with the antecedent true the
// solved value of b must fall inside [5, 10].
TEST(ConstraintImplication, ConsequentMayBeARangeConstraint) {
  ConstraintSolver solver(7);
  solver.AddVariable(Pinned("a", 0));
  RandVariable b;
  b.name = "b";
  b.min_val = 0;
  b.max_val = 100;
  solver.AddVariable(b);

  ConstraintBlock block;
  block.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "a";
  impl.cond_value = 0;
  ConstraintExpr cons;
  cons.kind = ConstraintKind::kRange;
  cons.var_name = "b";
  cons.lo = 5;
  cons.hi = 10;
  impl.sub_constraints.push_back(cons);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t bv = solver.GetValue("b");
  EXPECT_GE(bv, 5);
  EXPECT_LE(bv, 10);
}

// 18.5.5: the antecedent expression may be any integral expression, not just a
// simple equality. A general predicate antecedent ("mode > 100") drives the
// consequent: with mode pinned above 100 the antecedent holds, so len must be
// less than 10.
TEST(ConstraintImplication, GeneralExpressionAntecedentTrue) {
  ConstraintSolver solver(7);
  solver.AddVariable(Pinned("mode", 200));
  RandVariable len;
  len.name = "len";
  len.min_val = 0;
  len.max_val = 100;
  solver.AddVariable(len);

  ConstraintBlock block;
  block.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    auto it = vals.find("mode");
    return it != vals.end() && it->second > 100;
  };
  ConstraintExpr cons;
  cons.kind = ConstraintKind::kLessThan;
  cons.var_name = "len";
  cons.lo = 10;
  impl.sub_constraints.push_back(cons);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_LT(solver.GetValue("len"), 10);
}

// 18.5.5: with a general predicate antecedent that evaluates false, the
// consequent imposes nothing. mode is pinned to 50 so ("mode > 100") is false;
// len is pinned to a value the consequent would forbid, yet the solve succeeds.
TEST(ConstraintImplication, GeneralExpressionAntecedentFalse) {
  ConstraintSolver solver(7);
  solver.AddVariable(Pinned("mode", 50));
  solver.AddVariable(Pinned("len", 999));

  ConstraintBlock block;
  block.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_fn = [](const std::unordered_map<std::string, int64_t>& vals) {
    auto it = vals.find("mode");
    return it != vals.end() && it->second > 100;
  };
  ConstraintExpr cons;
  cons.kind = ConstraintKind::kLessThan;
  cons.var_name = "len";
  cons.lo = 10;
  impl.sub_constraints.push_back(cons);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("len"), 999);
}

// 18.5.5: when the antecedent holds, *every* constraint in the consequent must
// be satisfied, not merely the first. The antecedent (a == 0) is forced true
// and the consequent groups two constraints, so the solved values must satisfy
// both b == 1 and c == 2.
TEST(ConstraintImplication, AllConsequentConstraintsEnforced) {
  ConstraintSolver solver(7);
  solver.AddVariable(Pinned("a", 0));
  RandVariable b;
  b.name = "b";
  b.min_val = 0;
  b.max_val = 1;
  solver.AddVariable(b);
  RandVariable c;
  c.name = "c";
  c.min_val = 0;
  c.max_val = 3;
  solver.AddVariable(c);

  ConstraintBlock block;
  block.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "a";
  impl.cond_value = 0;
  ConstraintExpr c1;
  c1.kind = ConstraintKind::kEqual;
  c1.var_name = "b";
  c1.lo = 1;
  ConstraintExpr c2;
  c2.kind = ConstraintKind::kEqual;
  c2.var_name = "c";
  c2.lo = 2;
  impl.sub_constraints.push_back(c1);
  impl.sub_constraints.push_back(c2);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("b"), 1);
  EXPECT_EQ(solver.GetValue("c"), 2);
}

// 18.5.5: an implication is equivalent to (!a || b). When the antecedent is
// forced true and the consequent cannot be met, the implication is
// unsatisfiable, so randomization must report failure rather than hand back a
// solution that breaks the rule. Here a is pinned to 0 (antecedent true) while
// b is pinned to 0, so the consequent b == 1 can never hold.
TEST(ConstraintImplication,
     SolveFailsWhenForcedAntecedentHasImpossibleConsequent) {
  ConstraintSolver solver(7);
  solver.AddVariable(Pinned("a", 0));
  solver.AddVariable(Pinned("b", 0));

  ConstraintBlock block;
  block.name = "c_impl";
  ConstraintExpr impl;
  impl.kind = ConstraintKind::kImplication;
  impl.cond_var = "a";
  impl.cond_value = 0;
  ConstraintExpr cons;
  cons.kind = ConstraintKind::kEqual;
  cons.var_name = "b";
  cons.lo = 1;
  impl.sub_constraints.push_back(cons);
  block.constraints.push_back(impl);
  solver.AddConstraintBlock(block);

  EXPECT_FALSE(solver.Solve());
}

}  // namespace
