#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// A plain integral rand variable over [lo, hi] with the given bit width.
RandVariable MakeVar(const std::string& name, int64_t lo, int64_t hi,
                     uint32_t width = 8) {
  RandVariable v;
  v.name = name;
  v.min_val = lo;
  v.max_val = hi;
  v.width = width;
  return v;
}

// The LRM ordering example's constraint: 's -> d == 0'. When s is 1 the
// consequent forces d to 0; when s is 0 the implication imposes nothing.
ConstraintExpr SImpliesDZero() {
  ConstraintExpr c;
  c.kind = ConstraintKind::kImplication;
  c.cond_var = "s";
  c.cond_value = 1;
  ConstraintExpr d_eq_zero;
  d_eq_zero.kind = ConstraintKind::kEqual;
  d_eq_zero.var_name = "d";
  d_eq_zero.lo = 0;
  c.sub_constraints.push_back(d_eq_zero);
  return c;
}

// Build a solver for the 1-bit s / 2-bit d example with the 's -> d == 0'
// constraint. d ranges over {0,1,2,3}, so the legal combinations are the four
// (s=0, d) plus the single (s=1, d=0) — five in all.
ConstraintSolver MakeSdSolver(uint32_t seed) {
  ConstraintSolver solver(seed);
  solver.AddVariable(MakeVar("s", 0, 1, 1));
  solver.AddVariable(MakeVar("d", 0, 3, 2));
  ConstraintBlock blk;
  blk.name = "c";
  blk.constraints.push_back(SImpliesDZero());
  solver.AddConstraintBlock(blk);
  return solver;
}

// 18.5.9: with no ordering constraint the solver gives a uniform distribution
// over the legal value combinations — every legal (s, d) pair is equally
// probable. For the 's -> d == 0' example there are five legal combinations and
// s is 1 in only one of them, so without ordering s comes out 1 with probability
// near 1/5. The far-from-half observed frequency is what the ordering example
// then sets out to change.
TEST(VariableOrdering, UniformOverLegalCombinationsWithoutOrdering) {
  ConstraintSolver solver = MakeSdSolver(12345);
  int s_one = 0;
  const int kTrials = 600;
  for (int i = 0; i < kTrials; ++i) {
    ASSERT_TRUE(solver.Solve());
    if (solver.GetValue("s") == 1) ++s_one;
  }
  // Expected ~120 (1/5 of 600); a wide band keeps the statistical test stable
  // while still excluding the ordered ~1/2 behavior.
  EXPECT_GE(s_one, 60);
  EXPECT_LE(s_one, 190);
}

// 18.5.9: 'solve s before d' instructs the solver to choose s before d. The
// effect is that s is now chosen 0 or 1 with 50/50 probability, and d is then
// chosen subject to the value of s. The set of legal combinations is unchanged,
// but s is 1 about half the time rather than about a fifth — the distribution
// the ordering is meant to produce.
TEST(VariableOrdering, SolveBeforeShiftsDistributionTowardOrderedVariable) {
  ConstraintSolver solver = MakeSdSolver(12345);
  solver.AddSolveBefore({"s"}, {"d"});
  int s_one = 0;
  const int kTrials = 600;
  for (int i = 0; i < kTrials; ++i) {
    ASSERT_TRUE(solver.Solve());
    if (solver.GetValue("s") == 1) ++s_one;
  }
  // Expected ~300 (1/2 of 600), clearly separated from the ~120 of the
  // unordered case.
  EXPECT_GE(s_one, 240);
  EXPECT_LE(s_one, 360);
}

// 18.5.9: a 'solve ... before ...' constraint does not change the solution
// space. Every assignment the ordered solve produces is one of the same legal
// combinations the unordered solve admits, and the previously dominant
// combinations remain reachable — so both an s=0 result and the s=1 (with d=0)
// result still occur, and no illegal (s=1, d!=0) pair is ever produced.
TEST(VariableOrdering, OrderingPreservesSolutionSpace) {
  ConstraintSolver solver = MakeSdSolver(2024);
  solver.AddSolveBefore({"s"}, {"d"});
  bool saw_s0 = false;
  bool saw_s1 = false;
  for (int i = 0; i < 400; ++i) {
    ASSERT_TRUE(solver.Solve());
    int64_t s = solver.GetValue("s");
    int64_t d = solver.GetValue("d");
    if (s == 1) {
      saw_s1 = true;
      EXPECT_EQ(d, 0);  // the only legal d when s is 1
    } else {
      saw_s0 = true;
    }
  }
  EXPECT_TRUE(saw_s0);
  EXPECT_TRUE(saw_s1);
}

// 18.5.9: a 'solve ... before ...' constraint cannot cause the solver to fail.
// Even with the ordering in place, a satisfiable constraint set is always
// solved across many randomizations.
TEST(VariableOrdering, OrderingNeverCausesFailure) {
  ConstraintSolver solver = MakeSdSolver(777);
  solver.AddSolveBefore({"s"}, {"d"});
  for (int i = 0; i < 500; ++i) {
    EXPECT_TRUE(solver.Solve());
  }
}

// 18.5.9: ordering shifts probability but never overrides a hard constraint, so
// the solution space is still honored. Here a hard constraint pins the ordered
// variable s to 0; even though 'solve s before d' would otherwise let s be 0 or
// 1 with equal probability, committing s=1 admits no completion, so the solver
// keeps redrawing s until it lands on the only feasible value. s therefore comes
// out 0 every time and the solve always succeeds.
TEST(VariableOrdering, OrderingRespectsHardConstraintOnOrderedVariable) {
  ConstraintSolver solver(99);
  solver.AddVariable(MakeVar("s", 0, 1, 1));
  solver.AddVariable(MakeVar("d", 0, 3, 2));
  ConstraintBlock blk;
  blk.name = "c";
  blk.constraints.push_back(SImpliesDZero());
  ConstraintExpr s_zero;  // hard constraint: s == 0
  s_zero.kind = ConstraintKind::kEqual;
  s_zero.var_name = "s";
  s_zero.lo = 0;
  blk.constraints.push_back(s_zero);
  solver.AddConstraintBlock(blk);
  solver.AddSolveBefore({"s"}, {"d"});

  for (int i = 0; i < 200; ++i) {
    ASSERT_TRUE(solver.Solve());
    EXPECT_EQ(solver.GetValue("s"), 0);
  }
}

// 18.5.9: a variable that is not explicitly ordered is solved with the last set
// of ordered variables — that is, after the ordered head — so its value is
// conditioned on the earlier choice rather than chosen freely. With 'solve a
// before d', the head a is drawn first and so keeps a uniform 1/2 marginal,
// while the unordered u (constrained by 'u -> a == 0') is solved afterward: when
// a came out 1 the constraint forces u to 0, so u is 1 only when a is 0, giving a
// skewed ~1/4 marginal. The two marginals together show u is solved last (after
// a) rather than first; were u solved first it too would be uniform at ~1/2.
TEST(VariableOrdering, UnorderedVariableSolvedAfterOrderedHead) {
  ConstraintSolver solver(31);
  solver.AddVariable(MakeVar("a", 0, 1, 1));
  solver.AddVariable(MakeVar("d", 0, 1, 1));  // tail of the ordering (filler)
  solver.AddVariable(MakeVar("u", 0, 1, 1));  // not named in any ordering
  ConstraintBlock blk;
  blk.name = "c";
  ConstraintExpr u_implies_a_zero;  // u -> a == 0
  u_implies_a_zero.kind = ConstraintKind::kImplication;
  u_implies_a_zero.cond_var = "u";
  u_implies_a_zero.cond_value = 1;
  ConstraintExpr a_eq_zero;
  a_eq_zero.kind = ConstraintKind::kEqual;
  a_eq_zero.var_name = "a";
  a_eq_zero.lo = 0;
  u_implies_a_zero.sub_constraints.push_back(a_eq_zero);
  blk.constraints.push_back(u_implies_a_zero);
  solver.AddConstraintBlock(blk);
  solver.AddSolveBefore({"a"}, {"d"});

  int a_one = 0;
  int u_one = 0;
  const int kTrials = 800;
  for (int i = 0; i < kTrials; ++i) {
    ASSERT_TRUE(solver.Solve());
    if (solver.GetValue("a") == 1) ++a_one;
    if (solver.GetValue("u") == 1) ++u_one;
  }
  // a is the head: drawn first, uniform near 1/2 (~400).
  EXPECT_GE(a_one, 330);
  EXPECT_LE(a_one, 470);
  // u is unordered, solved last and conditioned: near 1/4 (~200), clearly below
  // the ~1/2 it would show if it were solved first.
  EXPECT_GE(u_one, 140);
  EXPECT_LE(u_one, 270);
}

// 18.5.9: variables that are partially ordered are solved with the latest set of
// ordered variables so that all ordering constraints are met. Here a and b are
// each ordered before c but unordered relative to each other, so they belong to
// the first solved set (each keeps a uniform 1/2 marginal) while c is solved in
// the final set. Because c is solved after both, the constraint 'c == a & b' is
// always met by the value chosen for c, so the solve never fails and c equals the
// committed a & b on every randomization.
TEST(VariableOrdering, PartiallyOrderedVariablesSolvedInFirstSet) {
  ConstraintSolver solver(17);
  solver.AddVariable(MakeVar("a", 0, 1, 1));
  solver.AddVariable(MakeVar("b", 0, 1, 1));
  solver.AddVariable(MakeVar("c", 0, 1, 1));
  ConstraintBlock blk;
  blk.name = "c";
  ConstraintExpr c_eq_a_and_b;
  c_eq_a_and_b.kind = ConstraintKind::kCustom;
  c_eq_a_and_b.eval_fn =
      [](const std::unordered_map<std::string, int64_t>& v) {
        auto a = v.find("a");
        auto b = v.find("b");
        auto c = v.find("c");
        if (a == v.end() || b == v.end() || c == v.end()) return true;
        return c->second == (a->second & b->second);
      };
  blk.constraints.push_back(c_eq_a_and_b);
  solver.AddConstraintBlock(blk);
  solver.AddSolveBefore({"a"}, {"c"});
  solver.AddSolveBefore({"b"}, {"c"});

  int a_one = 0;
  int b_one = 0;
  const int kTrials = 800;
  for (int i = 0; i < kTrials; ++i) {
    ASSERT_TRUE(solver.Solve());  // never fails: c is solved last to match a & b
    int64_t a = solver.GetValue("a");
    int64_t b = solver.GetValue("b");
    EXPECT_EQ(solver.GetValue("c"), a & b);  // c solved in the latest set
    if (a == 1) ++a_one;
    if (b == 1) ++b_one;
  }
  // a and b are in the first solved set: each uniform near 1/2 (~400).
  EXPECT_GE(a_one, 330);
  EXPECT_LE(a_one, 470);
  EXPECT_GE(b_one, 330);
  EXPECT_LE(b_one, 470);
}

// 18.5.9: each side of a 'solve ... before ...' ordering is a list of variables.
// 'solve a, b before c, d' orders every variable on the left ahead of every
// variable on the right, so a and b form the first solved set and c and d the
// last. With c constrained to equal a and d to equal b — relations the solver can
// always meet because c and d are chosen after a and b — the solve never fails,
// a and b keep their uniform marginals, and the dependent pair takes the matching
// committed values. This exercises the multi-variable list on both sides.
TEST(VariableOrdering, MultiVariableListsOrderedAcrossGroups) {
  ConstraintSolver solver(23);
  solver.AddVariable(MakeVar("a", 0, 1, 1));
  solver.AddVariable(MakeVar("b", 0, 1, 1));
  solver.AddVariable(MakeVar("c", 0, 1, 1));
  solver.AddVariable(MakeVar("d", 0, 1, 1));
  ConstraintBlock blk;
  blk.name = "c";
  ConstraintExpr deps;
  deps.kind = ConstraintKind::kCustom;
  deps.eval_fn = [](const std::unordered_map<std::string, int64_t>& v) {
    auto a = v.find("a");
    auto b = v.find("b");
    auto c = v.find("c");
    auto d = v.find("d");
    if (a == v.end() || b == v.end() || c == v.end() || d == v.end()) return true;
    return c->second == a->second && d->second == b->second;
  };
  blk.constraints.push_back(deps);
  solver.AddConstraintBlock(blk);
  solver.AddSolveBefore({"a", "b"}, {"c", "d"});

  int a_one = 0;
  int b_one = 0;
  const int kTrials = 800;
  for (int i = 0; i < kTrials; ++i) {
    ASSERT_TRUE(solver.Solve());  // c, d are solved last to match a, b
    int64_t a = solver.GetValue("a");
    int64_t b = solver.GetValue("b");
    EXPECT_EQ(solver.GetValue("c"), a);
    EXPECT_EQ(solver.GetValue("d"), b);
    if (a == 1) ++a_one;
    if (b == 1) ++b_one;
  }
  // a and b are the heads of the ordering: each uniform near 1/2 (~400).
  EXPECT_GE(a_one, 330);
  EXPECT_LE(a_one, 470);
  EXPECT_GE(b_one, 330);
  EXPECT_LE(b_one, 470);
}

}  // namespace
