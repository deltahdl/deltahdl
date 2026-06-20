#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_set>

#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// Build a plain integral rand variable over [lo, hi] with the given width.
RandVariable MakeVar(const std::string& name, int64_t lo, int64_t hi,
                     uint32_t width = 8) {
  RandVariable v;
  v.name = name;
  v.min_val = lo;
  v.max_val = hi;
  v.width = width;
  return v;
}

ConstraintBlock UniqueBlock(const std::vector<std::string>& members) {
  ConstraintBlock block;
  block.name = "u";
  ConstraintExpr c;
  c.kind = ConstraintKind::kUnique;
  c.unique_vars = members;
  block.constraints.push_back(c);
  return block;
}

// 18.5.4: a unique constraint requires that no two members of the group hold
// the same value after randomization. With three members confined to a domain
// that barely fits three distinct values, every solve yields three different
// values.
TEST(ConstraintUnique, MembersGetDistinctValues) {
  ConstraintSolver solver(7);
  solver.AddVariable(MakeVar("a", 0, 2));
  solver.AddVariable(MakeVar("b", 0, 2));
  solver.AddVariable(MakeVar("c", 0, 2));
  solver.AddConstraintBlock(UniqueBlock({"a", "b", "c"}));

  for (int i = 0; i < 50; ++i) {
    ASSERT_TRUE(solver.Solve());
    std::unordered_set<int64_t> seen{solver.GetValue("a"), solver.GetValue("b"),
                                     solver.GetValue("c")};
    EXPECT_EQ(seen.size(), 3u);
  }
}

// 18.5.4: when the domain is too small to give every member a distinct value,
// the uniqueness constraint cannot be satisfied and randomization fails.
TEST(ConstraintUnique, OverConstrainedGroupFails) {
  ConstraintSolver solver(7);
  solver.AddVariable(MakeVar("a", 0, 1));
  solver.AddVariable(MakeVar("b", 0, 1));
  solver.AddVariable(MakeVar("c", 0, 1));
  solver.AddConstraintBlock(UniqueBlock({"a", "b", "c"}));

  EXPECT_FALSE(solver.Solve());
}

// 18.5.4: if the group of variables contains fewer than two members the
// constraint shall have no effect and shall not cause a contradiction. A single
// member always solves and is free to take any value in its domain.
TEST(ConstraintUnique, SingleMemberHasNoEffect) {
  ConstraintSolver solver(7);
  solver.AddVariable(MakeVar("a", 0, 0));
  solver.AddConstraintBlock(UniqueBlock({"a"}));

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("a"), 0);
}

// 18.5.4: an empty group (also fewer than two members) likewise has no effect
// and never contradicts other constraints, even one pinning a variable to a
// fixed value.
TEST(ConstraintUnique, EmptyGroupCausesNoContradiction) {
  ConstraintSolver solver(7);
  RandVariable v = MakeVar("a", 0, 5);
  solver.AddVariable(v);

  ConstraintBlock block = UniqueBlock({});
  ConstraintExpr eq;
  eq.kind = ConstraintKind::kEqual;
  eq.var_name = "a";
  eq.lo = 4;
  block.constraints.push_back(eq);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("a"), 4);
}

// 18.5.4: no randc variable shall appear in the group. A unique group that
// names a randc member is illegal and makes randomization fail.
TEST(ConstraintUnique, RandcMemberFails) {
  ConstraintSolver solver(7);
  solver.AddVariable(MakeVar("a", 0, 7));
  RandVariable b = MakeVar("b", 0, 7);
  b.qualifier = RandQualifier::kRandc;
  solver.AddVariable(b);
  solver.AddConstraintBlock(UniqueBlock({"a", "b"}));

  EXPECT_FALSE(solver.Solve());
}

// 18.5.4: all members of the group shall be of equivalent type. A group that
// mixes members of different bit widths is not of equivalent type, so the
// constraint is illegal and randomization fails.
TEST(ConstraintUnique, MixedWidthMembersFail) {
  ConstraintSolver solver(7);
  solver.AddVariable(MakeVar("a", 0, 7, /*width=*/8));
  solver.AddVariable(MakeVar("b", 0, 7, /*width=*/16));
  solver.AddConstraintBlock(UniqueBlock({"a", "b"}));

  EXPECT_FALSE(solver.Solve());
}

// 18.5.4: a member of a unique group is of integral or real type, and all
// members shall be of equivalent type. A real member and an integral member are
// not of equivalent type, so a group mixing the two is illegal and
// randomization fails.
TEST(ConstraintUnique, MixedRealAndIntegralMembersFail) {
  ConstraintSolver solver(7);
  RandVariable a;
  a.name = "a";
  a.is_real = true;
  a.real_min = 0.0;
  a.real_max = 8.0;
  solver.AddVariable(a);
  solver.AddVariable(MakeVar("b", 0, 7));
  solver.AddConstraintBlock(UniqueBlock({"a", "b"}));

  EXPECT_FALSE(solver.Solve());
}

// 18.5.4: a group whose members agree on real-ness and width is of equivalent
// type and solves normally, confirming the equivalent-type check does not
// reject a well-formed group.
TEST(ConstraintUnique, EquivalentTypeMembersSolve) {
  ConstraintSolver solver(7);
  solver.AddVariable(MakeVar("a", 0, 7, /*width=*/8));
  solver.AddVariable(MakeVar("b", 0, 7, /*width=*/8));
  solver.AddConstraintBlock(UniqueBlock({"a", "b"}));

  ASSERT_TRUE(solver.Solve());
  EXPECT_NE(solver.GetValue("a"), solver.GetValue("b"));
}

}  // namespace
