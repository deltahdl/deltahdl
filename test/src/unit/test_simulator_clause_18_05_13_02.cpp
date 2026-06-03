#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// Add an integral rand variable spanning [min, max] to the solver.
void AddRand(ConstraintSolver& solver, const std::string& name, int64_t min,
             int64_t max) {
  RandVariable v;
  v.name = name;
  v.min_val = min;
  v.max_val = max;
  solver.AddVariable(v);
}

// Fill a caller-owned inner/soft pair so that 'soft' is a soft constraint
// wrapping the equality "var == val". The caller owns both objects so the
// soft wrapper's inner pointer stays valid for the lifetime of the solve.
void MakeSoftEq(ConstraintExpr& inner, ConstraintExpr& soft,
                const std::string& var, int64_t val) {
  inner.kind = ConstraintKind::kEqual;
  inner.var_name = var;
  inner.lo = val;
  soft.kind = ConstraintKind::kSoft;
  soft.var_name = var;
  soft.inner = &inner;
}

// Build a 'disable soft' directive on the named random variable.
ConstraintExpr MakeDisableSoft(const std::string& var) {
  ConstraintExpr c;
  c.kind = ConstraintKind::kDisableSoft;
  c.var_name = var;
  return c;
}

// 18.5.13.2: a 'disable soft' constraint on a random variable discards the
// lower-priority soft constraints that reference it. Here the only soft
// constraint, the satisfiable and non-contradicting x == 5, is declared before
// 'disable soft x' and is therefore discarded. The control (the same soft
// constraint without the directive) honors x == 5, while the reference solver
// (no soft constraint at all) shows the unconstrained draw; with the directive
// in place x takes that unconstrained value, confirming the soft preference was
// dropped rather than honored.
TEST(DisableSoftConstraint, DiscardsLowerPrioritySoftReferencingVariable) {
  ConstraintSolver control(42);
  AddRand(control, "x", 0, 100);
  ConstraintBlock cb;
  cb.name = "c";
  ConstraintExpr ci, cs;
  MakeSoftEq(ci, cs, "x", 5);
  cb.constraints.push_back(cs);
  control.AddConstraintBlock(cb);
  ASSERT_TRUE(control.Solve());
  EXPECT_EQ(control.GetValue("x"), 5);  // soft preference honored without disable

  ConstraintSolver reference(42);
  AddRand(reference, "x", 0, 100);  // no constraints: x is unconstrained
  ASSERT_TRUE(reference.Solve());

  ConstraintSolver solver(42);
  AddRand(solver, "x", 0, 100);
  ConstraintBlock b;
  b.name = "c";
  ConstraintExpr inner, soft;
  MakeSoftEq(inner, soft, "x", 5);
  b.constraints.push_back(soft);          // lower priority: declared first
  b.constraints.push_back(MakeDisableSoft("x"));  // discards the soft above
  solver.AddConstraintBlock(b);

  ASSERT_TRUE(solver.Solve());
  // The soft x == 5 was discarded, so x behaves exactly as the unconstrained
  // variable and is not biased toward 5.
  EXPECT_EQ(solver.GetValue("x"), reference.GetValue("x"));
}

// 18.5.13.2: only the *lower*-priority soft constraints are discarded. A soft
// constraint declared after the directive has higher priority and is left
// untouched. Here 'disable soft x' precedes the soft x == 8, which therefore
// survives and is honored.
TEST(DisableSoftConstraint, LeavesHigherPrioritySoftUntouched) {
  ConstraintSolver solver(42);
  AddRand(solver, "x", 0, 100);

  ConstraintBlock b;
  b.name = "c";
  b.constraints.push_back(MakeDisableSoft("x"));  // directive declared first
  ConstraintExpr inner, soft;
  MakeSoftEq(inner, soft, "x", 8);  // higher priority: declared after directive
  b.constraints.push_back(soft);
  solver.AddConstraintBlock(b);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 8);
}

// 18.5.13.2: a 'disable soft' constraint discards lower-priority soft
// constraints regardless of whether they contradict anything. The soft x == 5
// is jointly satisfiable with the independent soft y == 7 (no contradiction),
// so the 18.5.13.1 priority resolution alone would keep it; the directive
// discards it anyway. y == 7, which does not reference x, is still honored, and
// x falls back to its unconstrained value.
TEST(DisableSoftConstraint, DiscardsNonContradictingSoft) {
  ConstraintSolver control(7);
  AddRand(control, "x", 0, 100);
  AddRand(control, "y", 0, 100);
  ConstraintBlock cb;
  cb.name = "c";
  ConstraintExpr cxi, cxs;
  MakeSoftEq(cxi, cxs, "x", 5);
  cb.constraints.push_back(cxs);
  ConstraintExpr cyi, cys;
  MakeSoftEq(cyi, cys, "y", 7);
  cb.constraints.push_back(cys);
  control.AddConstraintBlock(cb);
  ASSERT_TRUE(control.Solve());
  EXPECT_EQ(control.GetValue("x"), 5);  // both soft preferences honored, no disable
  EXPECT_EQ(control.GetValue("y"), 7);

  ConstraintSolver reference(7);
  AddRand(reference, "x", 0, 100);
  AddRand(reference, "y", 0, 100);
  ConstraintBlock rb;
  rb.name = "c";
  ConstraintExpr ryi, rys;  // only the y preference; x left unconstrained
  MakeSoftEq(ryi, rys, "y", 7);
  rb.constraints.push_back(rys);
  reference.AddConstraintBlock(rb);
  ASSERT_TRUE(reference.Solve());

  ConstraintSolver solver(7);
  AddRand(solver, "x", 0, 100);
  AddRand(solver, "y", 0, 100);
  ConstraintBlock b;
  b.name = "c";
  ConstraintExpr xi, xs;
  MakeSoftEq(xi, xs, "x", 5);
  b.constraints.push_back(xs);
  ConstraintExpr yi, ys;
  MakeSoftEq(yi, ys, "y", 7);
  b.constraints.push_back(ys);
  b.constraints.push_back(MakeDisableSoft("x"));  // discards x == 5 only
  solver.AddConstraintBlock(b);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("y"), 7);  // unrelated soft still honored
  // x == 5 was discarded even though it did not contradict anything.
  EXPECT_EQ(solver.GetValue("x"), reference.GetValue("x"));
}

// 18.5.13.2: a 'disable soft' constraint only disables soft constraints in
// which the referenced variable directly appears. This soft constraint
// constrains q (q == 7) and does not directly reference p — modeling the
// consequent of p -> soft q, where p only gates the constraint. 'disable soft
// p' therefore leaves it in place and q == 7 is honored.
TEST(DisableSoftConstraint, SkipsSoftWhereVariableNotDirect) {
  ConstraintSolver solver(11);
  AddRand(solver, "p", 0, 100);
  AddRand(solver, "q", 0, 100);

  ConstraintBlock b;
  b.name = "c";
  ConstraintExpr inner, soft;
  MakeSoftEq(inner, soft, "q", 7);  // directly references q only, not p
  b.constraints.push_back(soft);
  b.constraints.push_back(MakeDisableSoft("p"));  // p is not directly in the soft
  solver.AddConstraintBlock(b);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("q"), 7);
}

// 18.5.13.2: conversely, when the disabled variable does appear directly in a
// soft constraint, that constraint is discarded. This soft constraint directly
// references both p and q (modeling soft !p || q), recorded in its ref_vars.
// 'disable soft p' discards it, so q is no longer biased toward 7 and takes its
// unconstrained value; the control without the directive honors q == 7.
TEST(DisableSoftConstraint, DiscardsSoftWithDirectMultiVarReference) {
  ConstraintSolver control(11);
  AddRand(control, "p", 0, 100);
  AddRand(control, "q", 0, 100);
  ConstraintBlock cb;
  cb.name = "c";
  ConstraintExpr ci, cs;
  MakeSoftEq(ci, cs, "q", 7);
  cs.ref_vars = {"p", "q"};  // directly references both p and q
  cb.constraints.push_back(cs);
  control.AddConstraintBlock(cb);
  ASSERT_TRUE(control.Solve());
  EXPECT_EQ(control.GetValue("q"), 7);  // honored without the directive

  ConstraintSolver reference(11);
  AddRand(reference, "p", 0, 100);
  AddRand(reference, "q", 0, 100);  // both unconstrained
  ASSERT_TRUE(reference.Solve());

  ConstraintSolver solver(11);
  AddRand(solver, "p", 0, 100);
  AddRand(solver, "q", 0, 100);
  ConstraintBlock b;
  b.name = "c";
  ConstraintExpr inner, soft;
  MakeSoftEq(inner, soft, "q", 7);
  soft.ref_vars = {"p", "q"};
  b.constraints.push_back(soft);
  b.constraints.push_back(MakeDisableSoft("p"));  // p appears directly: discard
  solver.AddConstraintBlock(b);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("q"), reference.GetValue("q"));
}

// 18.5.13.2: the directive applies to an array's size variable too — the clause
// names array.size explicitly. A soft constraint preferring the size be 4 is
// discarded by 'disable soft' on that same size variable, so the size returns to
// its unconstrained value; the control without the directive honors size == 4.
TEST(DisableSoftConstraint, AppliesToArraySizeVariable) {
  ConstraintSolver control(99);
  RandVariable cv;
  cv.name = "arr.size";
  cv.min_val = 0;
  cv.max_val = 100;
  cv.is_array_size = true;
  control.AddVariable(cv);
  ConstraintBlock cb;
  cb.name = "c";
  ConstraintExpr ci, cs;
  MakeSoftEq(ci, cs, "arr.size", 4);
  cb.constraints.push_back(cs);
  control.AddConstraintBlock(cb);
  ASSERT_TRUE(control.Solve());
  EXPECT_EQ(control.GetValue("arr.size"), 4);

  ConstraintSolver reference(99);
  RandVariable rv;
  rv.name = "arr.size";
  rv.min_val = 0;
  rv.max_val = 100;
  rv.is_array_size = true;
  reference.AddVariable(rv);  // unconstrained size
  ASSERT_TRUE(reference.Solve());

  ConstraintSolver solver(99);
  RandVariable v;
  v.name = "arr.size";
  v.min_val = 0;
  v.max_val = 100;
  v.is_array_size = true;
  solver.AddVariable(v);
  ConstraintBlock b;
  b.name = "c";
  ConstraintExpr inner, soft;
  MakeSoftEq(inner, soft, "arr.size", 4);
  b.constraints.push_back(soft);
  b.constraints.push_back(MakeDisableSoft("arr.size"));
  solver.AddConstraintBlock(b);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("arr.size"), reference.GetValue("arr.size"));
}

// 18.5.13.2: priority — and therefore which constraints count as lower
// priority — spans the whole enclosing construct, not a single block. A
// 'disable soft' directive in a later constraint block has higher priority than
// a soft constraint in an earlier block, so it discards that earlier soft. Here
// the first block prefers x == 5 and a second block carries 'disable soft x';
// the earlier preference is discarded and x returns to its unconstrained value,
// matching the reference solve with no soft constraint at all.
TEST(DisableSoftConstraint, DiscardsSoftInEarlierConstraintBlock) {
  ConstraintSolver reference(5);
  AddRand(reference, "x", 0, 100);  // unconstrained
  ASSERT_TRUE(reference.Solve());

  ConstraintSolver solver(5);
  AddRand(solver, "x", 0, 100);
  ConstraintBlock first;
  first.name = "c_first";
  ConstraintExpr inner, soft;
  MakeSoftEq(inner, soft, "x", 5);  // earlier block: lower priority
  first.constraints.push_back(soft);
  solver.AddConstraintBlock(first);
  ConstraintBlock second;
  second.name = "c_second";
  second.constraints.push_back(MakeDisableSoft("x"));  // later block: discards it
  solver.AddConstraintBlock(second);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), reference.GetValue("x"));
}

// 18.5.13.2: a 'disable soft' directive discards *all* lower-priority soft
// constraints that reference the variable, not merely the nearest one. Two
// lower-priority preferences apply to x — x == 5 and x inside {5, 6, 7} — and a
// single 'disable soft x' discards both, leaving x fully unconstrained. The
// reference solve (no soft constraint) confirms x is not still pinned to 5 nor
// confined to the set; were either preference left in place, x would differ
// from the unconstrained draw.
TEST(DisableSoftConstraint, DiscardsAllLowerPrioritySoftReferencingVariable) {
  ConstraintSolver reference(31);
  AddRand(reference, "x", 0, 100);  // unconstrained
  ASSERT_TRUE(reference.Solve());

  ConstraintSolver solver(31);
  AddRand(solver, "x", 0, 100);
  ConstraintBlock b;
  b.name = "c";
  ConstraintExpr ei, es;
  MakeSoftEq(ei, es, "x", 5);  // first lower-priority soft
  b.constraints.push_back(es);
  ConstraintExpr si;  // second lower-priority soft: x inside {5, 6, 7}
  si.kind = ConstraintKind::kSetMembership;
  si.var_name = "x";
  si.set_values = {5, 6, 7};
  ConstraintExpr ss;
  ss.kind = ConstraintKind::kSoft;
  ss.var_name = "x";
  ss.inner = &si;
  b.constraints.push_back(ss);
  b.constraints.push_back(MakeDisableSoft("x"));  // discards both of the above
  solver.AddConstraintBlock(b);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), reference.GetValue("x"));
}

// 18.5.13.2: a 'disable soft' directive supplied through an inline (with)
// constraint discards the class's lower-priority soft constraints. The class
// block prefers x == 5; the inline directive 'disable soft x', being of higher
// priority than the class constraints, discards it. x then takes its
// unconstrained value, matching the reference solve that applies neither.
TEST(DisableSoftConstraint, InlineDisableSoftDiscardsClassSoft) {
  ConstraintSolver reference(17);
  AddRand(reference, "x", 0, 100);  // unconstrained
  ASSERT_TRUE(reference.SolveWith({}));

  ConstraintSolver solver(17);
  AddRand(solver, "x", 0, 100);
  ConstraintBlock b;
  b.name = "c_class";
  ConstraintExpr inner, soft;
  MakeSoftEq(inner, soft, "x", 5);  // class soft: lower priority
  b.constraints.push_back(soft);
  solver.AddConstraintBlock(b);

  std::vector<ConstraintExpr> inline_constraints = {MakeDisableSoft("x")};
  ASSERT_TRUE(solver.SolveWith(inline_constraints));
  EXPECT_EQ(solver.GetValue("x"), reference.GetValue("x"));
}

}
