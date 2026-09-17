#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// A plain integral rand variable over [lo, hi].
RandVariable MakeVar(const std::string& name, int64_t lo, int64_t hi) {
  RandVariable v;
  v.name = name;
  v.min_val = lo;
  v.max_val = hi;
  v.width = 8;
  return v;
}

// A single-variable equality constraint, used as a per-element foreach body or
// as a top-level hard constraint pinning a value.
ConstraintExpr Eq(const std::string& name, int64_t value) {
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = name;
  c.lo = value;
  return c;
}

// 18.5.7.1: a foreach iterative constraint applies its constraint_set to the
// elements of the array. For a fixed-size array (no size variable), every
// per-element constraint is imposed.
TEST(ForeachIterativeConstraint, AppliesConstraintToEveryElement) {
  ConstraintSolver solver(42);
  for (int i = 0; i < 3; ++i)
    solver.AddVariable(MakeVar("e" + std::to_string(i), -10, 10));

  ConstraintBlock block;
  block.name = "fc";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  for (int i = 0; i < 3; ++i) {
    ConstraintExpr gt;
    gt.kind = ConstraintKind::kGreaterThan;
    gt.var_name = "e" + std::to_string(i);
    gt.lo = 0;
    fe.sub_constraints.push_back(gt);
  }
  block.constraints.push_back(fe);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  for (int i = 0; i < 3; ++i)
    EXPECT_GT(solver.GetValue("e" + std::to_string(i)), 0);
}

// 18.5.7.1: an array's size method is a state variable within the foreach
// block. With the size pinned to 2, the iterative constraint applies only to
// the two elements that exist (indices 0 and 1); the remaining elements are not
// iterated, so their conflicting hard constraints can be satisfied. Were the
// foreach to ignore the size and constrain all four elements, e2 == 0 would
// clash with the hard e2 == 1 and randomization would fail.
TEST(ForeachIterativeConstraint, SizeLimitsIteratedElements) {
  ConstraintSolver solver(7);
  RandVariable n = MakeVar("n", 2, 2);
  n.is_array_size = true;
  solver.AddVariable(n);
  for (int i = 0; i < 4; ++i)
    solver.AddVariable(MakeVar("e" + std::to_string(i), 0, 1));

  // foreach (arr[i]) arr[i] == 0;  -- over a dynamically sized array 'arr'.
  ConstraintBlock fb;
  fb.name = "fc";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  fe.size_var = "n";
  for (int i = 0; i < 4; ++i)
    fe.sub_constraints.push_back(Eq("e" + std::to_string(i), 0));
  fb.constraints.push_back(fe);
  solver.AddConstraintBlock(fb);

  // Hard constraints on the elements beyond the current size.
  ConstraintBlock hb;
  hb.name = "tail";
  hb.constraints.push_back(Eq("e2", 1));
  hb.constraints.push_back(Eq("e3", 1));
  solver.AddConstraintBlock(hb);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("n"), 2);
  EXPECT_EQ(solver.GetValue("e0"), 0);  // iterated: foreach imposed e0 == 0
  EXPECT_EQ(solver.GetValue("e1"), 0);  // iterated: foreach imposed e1 == 0
  EXPECT_EQ(solver.GetValue("e2"), 1);  // beyond size: foreach did not apply
  EXPECT_EQ(solver.GetValue("e3"), 1);  // beyond size: foreach did not apply
}

// 18.5.7.1: the size constraints are solved first and the iterative constraints
// next; the size method behaves as a state variable in the foreach. Here the
// size is itself random — its domain is [0:5] but a separate size constraint
// confines it to 1 (A.size as a random variable). The foreach then reads that
// committed value and constrains exactly the one element that exists, leaving
// the trailing element (which carries a conflicting hard constraint) free.
TEST(ForeachIterativeConstraint, SizeConstraintSolvedBeforeIteration) {
  ConstraintSolver solver(123);
  RandVariable n = MakeVar("n", 0, 5);
  n.is_array_size = true;
  solver.AddVariable(n);
  solver.AddVariable(MakeVar("e0", 0, 1));
  solver.AddVariable(MakeVar("e1", 0, 1));

  // Size constraint: n inside [1:1] (A.size is a random variable here).
  ConstraintBlock sb;
  sb.name = "size_c";
  ConstraintExpr sz;
  sz.kind = ConstraintKind::kRange;
  sz.var_name = "n";
  sz.lo = 1;
  sz.hi = 1;
  sb.constraints.push_back(sz);
  solver.AddConstraintBlock(sb);

  // Iterative constraint: foreach (arr[i]) arr[i] == 0 (A.size is a state var).
  ConstraintBlock fb;
  fb.name = "fc";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  fe.size_var = "n";
  fe.sub_constraints.push_back(Eq("e0", 0));
  fe.sub_constraints.push_back(Eq("e1", 0));
  fb.constraints.push_back(fe);
  solver.AddConstraintBlock(fb);

  // Hard constraint on the trailing element (beyond the chosen size of 1).
  ConstraintBlock hb;
  hb.name = "tail";
  hb.constraints.push_back(Eq("e1", 1));
  solver.AddConstraintBlock(hb);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("n"), 1);
  EXPECT_EQ(solver.GetValue("e0"), 0);  // iterated: foreach imposed e0 == 0
  EXPECT_EQ(solver.GetValue("e1"), 1);  // beyond size: foreach did not apply
}

// 18.5.7.1: when the array's size equals the number of elements, the foreach
// iterates over all of them, so every per-element constraint is imposed. The
// size method is still read as a state variable to bound the iteration; here
// that bound covers the whole array, in contrast to the cases above where it
// excludes the trailing elements.
TEST(ForeachIterativeConstraint, SizeEqualToElementCountConstrainsAll) {
  ConstraintSolver solver(5);
  RandVariable n = MakeVar("n", 3, 3);
  n.is_array_size = true;
  solver.AddVariable(n);
  for (int i = 0; i < 3; ++i)
    solver.AddVariable(MakeVar("e" + std::to_string(i), -10, 10));

  ConstraintBlock fb;
  fb.name = "fc";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  fe.size_var = "n";
  for (int i = 0; i < 3; ++i) {
    ConstraintExpr gt;
    gt.kind = ConstraintKind::kGreaterThan;
    gt.var_name = "e" + std::to_string(i);
    gt.lo = 0;
    fe.sub_constraints.push_back(gt);
  }
  fb.constraints.push_back(fe);
  solver.AddConstraintBlock(fb);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("n"), 3);
  for (int i = 0; i < 3; ++i)
    EXPECT_GT(solver.GetValue("e" + std::to_string(i)), 0);
}

// 18.5.7.1: when the size method is zero, the foreach iterates over no
// elements, so even a per-element constraint that is impossible in isolation
// imposes nothing and randomization succeeds.
TEST(ForeachIterativeConstraint, ZeroSizeMakesForeachVacuous) {
  ConstraintSolver solver(99);
  RandVariable n = MakeVar("n", 0, 0);
  n.is_array_size = true;
  solver.AddVariable(n);
  solver.AddVariable(MakeVar("e0", 0, 1));

  ConstraintBlock fb;
  fb.name = "fc";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  fe.size_var = "n";
  // An unsatisfiable per-element constraint: e0 in [5:5] is outside its domain.
  ConstraintExpr impossible;
  impossible.kind = ConstraintKind::kRange;
  impossible.var_name = "e0";
  impossible.lo = 5;
  impossible.hi = 5;
  fe.sub_constraints.push_back(impossible);
  fb.constraints.push_back(fe);
  solver.AddConstraintBlock(fb);

  EXPECT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("n"), 0);
}

// 18.5.7.1: the clause's sorted array, a foreach over a dynamic array of
// ints holding each element above the one before it under the guard that
// keeps the index below the size, which the size constraint draws from 1 to
// 10: each consequent derives the bound its element is drawn above, so every
// one of 128 solves is ascending over the size drawn, which the draws tried
// against the relations as a whole meet as good as never, and every size
// from 1 to 10 is drawn.
TEST(ForeachIterativeConstraint, GuardedChainOverDrawnSizeIsRepaired) {
  ConstraintSolver solver(3);
  RandVariable n = MakeVar("n", 0, 10);
  n.width = 32;
  n.is_array_size = true;
  solver.AddVariable(n);
  for (int i = 0; i < 10; ++i) {
    RandVariable e =
        MakeVar("e" + std::to_string(i), -2147483648LL, 2147483647LL);
    e.width = 32;
    solver.AddVariable(e);
  }
  ConstraintBlock sb;
  sb.name = "size_c";
  ConstraintExpr sz;
  sz.kind = ConstraintKind::kSetMembership;
  sz.var_name = "n";
  for (int i = 1; i <= 10; ++i) sz.set_values.push_back(i);
  sz.ref_vars.push_back("n");
  sb.constraints.push_back(sz);
  solver.AddConstraintBlock(sb);
  ConstraintBlock fb;
  fb.name = "fc";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  fe.size_var = "n";
  for (int k = 0; k < 10; ++k) {
    std::string lo = "e" + std::to_string(k);
    std::string hi = "e" + std::to_string(k + 1);
    ConstraintExpr rel;
    rel.kind = ConstraintKind::kCustom;
    rel.var_name = hi;
    rel.ref_vars = {lo, hi};
    rel.eval_fn = [lo, hi](const std::unordered_map<std::string, int64_t>& v) {
      return v.at(hi) > v.at(lo);
    };
    rel.derive_fn = [lo](const std::unordered_map<std::string, int64_t>& v) {
      return v.at(lo);
    };
    rel.derive_cmp = ConstraintKind::kGreaterThan;
    ConstraintExpr imp;
    imp.kind = ConstraintKind::kImplication;
    imp.cond_fn = [k](const std::unordered_map<std::string, int64_t>& v) {
      return k < v.at("n") - 1;
    };
    imp.sub_constraints.push_back(rel);
    fe.sub_constraints.push_back(imp);
  }
  fb.constraints.push_back(fe);
  solver.AddConstraintBlock(fb);

  unsigned sizes_seen = 0;
  for (int draw = 0; draw < 128; ++draw) {
    ASSERT_TRUE(solver.Solve());
    int64_t size = solver.GetValue("n");
    ASSERT_GE(size, 1);
    ASSERT_LE(size, 10);
    sizes_seen |= 1u << size;
    for (int64_t i = 1; i < size; ++i) {
      EXPECT_GT(solver.GetValue("e" + std::to_string(i)),
                solver.GetValue("e" + std::to_string(i - 1)));
    }
  }
  EXPECT_EQ(sizes_seen, 0x7FEu);
}

}  // namespace
