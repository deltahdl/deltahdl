#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

RandVariable MakeVar(const std::string& name, int64_t lo, int64_t hi) {
  RandVariable v;
  v.name = name;
  v.min_val = lo;
  v.max_val = hi;
  v.width = 8;
  return v;
}

ConstraintExpr Eq(const std::string& name, int64_t value) {
  ConstraintExpr c;
  c.kind = ConstraintKind::kEqual;
  c.var_name = name;
  c.lo = value;
  return c;
}

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

TEST(ForeachIterativeConstraint, SizeLimitsIteratedElements) {
  ConstraintSolver solver(7);
  RandVariable n = MakeVar("n", 2, 2);
  n.is_array_size = true;
  solver.AddVariable(n);
  for (int i = 0; i < 4; ++i)
    solver.AddVariable(MakeVar("e" + std::to_string(i), 0, 1));

  ConstraintBlock fb;
  fb.name = "fc";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  fe.size_var = "n";
  for (int i = 0; i < 4; ++i)
    fe.sub_constraints.push_back(Eq("e" + std::to_string(i), 0));
  fb.constraints.push_back(fe);
  solver.AddConstraintBlock(fb);

  ConstraintBlock hb;
  hb.name = "tail";
  hb.constraints.push_back(Eq("e2", 1));
  hb.constraints.push_back(Eq("e3", 1));
  solver.AddConstraintBlock(hb);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("n"), 2);
  EXPECT_EQ(solver.GetValue("e0"), 0);
  EXPECT_EQ(solver.GetValue("e1"), 0);
  EXPECT_EQ(solver.GetValue("e2"), 1);
  EXPECT_EQ(solver.GetValue("e3"), 1);
}

TEST(ForeachIterativeConstraint, SizeConstraintSolvedBeforeIteration) {
  ConstraintSolver solver(123);
  RandVariable n = MakeVar("n", 0, 5);
  n.is_array_size = true;
  solver.AddVariable(n);
  solver.AddVariable(MakeVar("e0", 0, 1));
  solver.AddVariable(MakeVar("e1", 0, 1));

  ConstraintBlock sb;
  sb.name = "size_c";
  ConstraintExpr sz;
  sz.kind = ConstraintKind::kRange;
  sz.var_name = "n";
  sz.lo = 1;
  sz.hi = 1;
  sb.constraints.push_back(sz);
  solver.AddConstraintBlock(sb);

  ConstraintBlock fb;
  fb.name = "fc";
  ConstraintExpr fe;
  fe.kind = ConstraintKind::kForeach;
  fe.size_var = "n";
  fe.sub_constraints.push_back(Eq("e0", 0));
  fe.sub_constraints.push_back(Eq("e1", 0));
  fb.constraints.push_back(fe);
  solver.AddConstraintBlock(fb);

  ConstraintBlock hb;
  hb.name = "tail";
  hb.constraints.push_back(Eq("e1", 1));
  solver.AddConstraintBlock(hb);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("n"), 1);
  EXPECT_EQ(solver.GetValue("e0"), 0);
  EXPECT_EQ(solver.GetValue("e1"), 1);
}

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
