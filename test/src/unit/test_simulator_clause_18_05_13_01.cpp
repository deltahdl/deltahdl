#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <unordered_set>
#include <vector>

#include "helpers_constraint_soft.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// 18.5.13.1: when two soft constraints contradict each other, they are not both
// discarded; the higher-priority one prevails. Priority follows declaration
// order — a constraint declared later in the construct has higher priority — so
// of the two mutually exclusive preferences x == 10 (declared first) and
// x == 20 (declared later), the solver retains the later, higher-priority
// x == 20 and discards x == 10. This is the "c1 only" branch of the clause's
// conceptual model, where c1 is the higher-priority constraint.
TEST(SoftConstraintPriority, HigherPrioritySoftConstraintPrevails) {
  ConstraintSolver solver(42);
  AddRand(solver, "x", 0, 100);

  ConstraintBlock block;
  block.name = "c_soft";
  ConstraintExpr inner_lo, soft_lo;  // x == 10, lower priority (declared first)
  MakeSoftEq(inner_lo, soft_lo, "x", 10);
  block.constraints.push_back(soft_lo);
  ConstraintExpr inner_hi,
      soft_hi;  // x == 20, higher priority (declared later)
  MakeSoftEq(inner_hi, soft_hi, "x", 20);
  block.constraints.push_back(soft_hi);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 20);
}

// 18.5.13.1: priority by declaration order spans the whole enclosing construct,
// not just one block — a soft constraint in a constraint block declared later
// in the class outranks one in an earlier block. Two separate blocks each
// prefer a contradictory value for x; the later block's preference (x == 20)
// prevails over the earlier block's (x == 10).
TEST(SoftConstraintPriority, LaterConstraintBlockOutranksEarlierBlock) {
  ConstraintSolver solver(64);
  AddRand(solver, "x", 0, 100);

  ConstraintBlock first;
  first.name = "c_first";
  ConstraintExpr inner_lo, soft_lo;  // earlier block: x == 10 (lower priority)
  MakeSoftEq(inner_lo, soft_lo, "x", 10);
  first.constraints.push_back(soft_lo);
  solver.AddConstraintBlock(first);

  ConstraintBlock second;
  second.name = "c_second";
  ConstraintExpr inner_hi, soft_hi;  // later block: x == 20 (higher priority)
  MakeSoftEq(inner_hi, soft_hi, "x", 20);
  second.constraints.push_back(soft_hi);
  solver.AddConstraintBlock(second);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 20);
}

// 18.5.13.1: a higher-priority soft constraint that cannot be honored does not
// block a lower-priority one that can be. The hard range [0, 30] rules out the
// higher-priority preference x == 100 (declared later), so the solver discards
// it but still honors the lower-priority, satisfiable x == 15 (declared first).
// This is the "c2 only" branch of the conceptual model.
TEST(SoftConstraintPriority, LowerPrioritySoftHonoredWhenHigherConflictsHard) {
  ConstraintSolver solver(7);
  AddRand(solver, "x", 0, 100);

  ConstraintBlock b_hard;
  b_hard.name = "c_range";
  ConstraintExpr hc;
  hc.kind = ConstraintKind::kRange;
  hc.var_name = "x";
  hc.lo = 0;
  hc.hi = 30;
  b_hard.constraints.push_back(hc);
  solver.AddConstraintBlock(b_hard);

  ConstraintBlock b_soft;
  b_soft.name = "c_soft";
  ConstraintExpr inner_lo, soft_lo;  // x == 15, lower priority, in hard range
  MakeSoftEq(inner_lo, soft_lo, "x", 15);
  b_soft.constraints.push_back(soft_lo);
  ConstraintExpr inner_hi, soft_hi;  // x == 100, higher priority, outside range
  MakeSoftEq(inner_hi, soft_hi, "x", 100);
  b_soft.constraints.push_back(soft_hi);
  solver.AddConstraintBlock(b_soft);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 15);
}

// 18.5.13.1: the final fallback of the conceptual model — when neither soft
// constraint can be honored, both are discarded. The hard range [0, 5] rules
// out both the lower-priority x == 50 and the higher-priority x == 90, so
// neither survives the priority resolution; the call still succeeds against the
// hard constraint alone, and neither discarded preference is honored.
TEST(SoftConstraintPriority, BothSoftConstraintsDiscardedWhenNeitherCanHold) {
  ConstraintSolver solver(21);
  AddRand(solver, "x", 0, 100);

  ConstraintBlock b_hard;
  b_hard.name = "c_range";
  ConstraintExpr hc;
  hc.kind = ConstraintKind::kRange;
  hc.var_name = "x";
  hc.lo = 0;
  hc.hi = 5;
  b_hard.constraints.push_back(hc);
  solver.AddConstraintBlock(b_hard);

  ConstraintBlock b_soft;
  b_soft.name = "c_soft";
  ConstraintExpr inner_lo, soft_lo;  // x == 50, outside the hard range
  MakeSoftEq(inner_lo, soft_lo, "x", 50);
  b_soft.constraints.push_back(soft_lo);
  ConstraintExpr inner_hi, soft_hi;  // x == 90, also outside the hard range
  MakeSoftEq(inner_hi, soft_hi, "x", 90);
  b_soft.constraints.push_back(soft_hi);
  solver.AddConstraintBlock(b_soft);

  ASSERT_TRUE(solver.Solve());
  EXPECT_GE(solver.GetValue("x"), 0);
  EXPECT_LE(solver.GetValue("x"), 5);
  EXPECT_NE(solver.GetValue("x"), 50);
  EXPECT_NE(solver.GetValue("x"), 90);
}

// 18.5.13.1: a soft constraint within an inline (with) constraint block has
// higher priority than the constraints of the class being randomized. The class
// block prefers x == 10 and the inline block prefers x == 20; the two
// contradict, so the inline preference wins and the class one is discarded.
TEST(SoftConstraintPriority, InlineSoftConstraintOutranksClassSoft) {
  ConstraintSolver solver(13);
  AddRand(solver, "x", 0, 100);

  ConstraintBlock block;
  block.name = "c_class";
  ConstraintExpr inner_cls, soft_cls;  // class: x == 10
  MakeSoftEq(inner_cls, soft_cls, "x", 10);
  block.constraints.push_back(soft_cls);
  solver.AddConstraintBlock(block);

  ConstraintExpr inner_inl, soft_inl;  // inline: x == 20 (higher priority)
  MakeSoftEq(inner_inl, soft_inl, "x", 20);
  std::vector<ConstraintExpr> inline_constraints = {soft_inl};

  ASSERT_TRUE(solver.SolveWith(inline_constraints));
  EXPECT_EQ(solver.GetValue("x"), 20);
}

// 18.5.13.1: of three mutually exclusive soft preferences, only the
// highest-priority one survives the priority resolution. Declared in the order
// x == 10, x == 20, x == 30, the last has the highest priority, so the solver
// retains x == 30 and discards the other two. This shows the resolution
// generalizes beyond two constraints.
TEST(SoftConstraintPriority, HighestOfSeveralConflictingSoftConstraintsWins) {
  ConstraintSolver solver(99);
  AddRand(solver, "x", 0, 100);

  ConstraintBlock block;
  block.name = "c_soft";
  ConstraintExpr i0, s0;
  MakeSoftEq(i0, s0, "x", 10);
  block.constraints.push_back(s0);
  ConstraintExpr i1, s1;
  MakeSoftEq(i1, s1, "x", 20);
  block.constraints.push_back(s1);
  ConstraintExpr i2, s2;
  MakeSoftEq(i2, s2, "x", 30);
  block.constraints.push_back(s2);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 30);
}

// 18.5.13.1: if a call to randomize() involves only soft constraints, it can
// never fail. Here several soft preferences apply with no hard constraint to
// satisfy: two of them (x == 1 and x == 2) contradict each other while a third
// (y == 5) is independent. Rather than failing, the solver resolves the
// conflict by priority — the call succeeds, honoring the higher-priority x == 2
// of the contradictory pair and the independent y == 5.
TEST(SoftConstraintPriority, RandomizeWithOnlySoftConstraintsNeverFails) {
  ConstraintSolver solver(3);
  AddRand(solver, "x", 0, 100);
  AddRand(solver, "y", 0, 100);

  ConstraintBlock block;
  block.name = "c_soft";
  ConstraintExpr ix1, sx1;  // x == 1, lower priority of the contradictory pair
  MakeSoftEq(ix1, sx1, "x", 1);
  block.constraints.push_back(sx1);
  ConstraintExpr ix2, sx2;  // x == 2, higher priority (declared later)
  MakeSoftEq(ix2, sx2, "x", 2);
  block.constraints.push_back(sx2);
  ConstraintExpr iy, sy;  // y == 5, independent of the conflict
  MakeSoftEq(iy, sy, "y", 5);
  block.constraints.push_back(sy);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 2);
  EXPECT_EQ(solver.GetValue("y"), 5);
}

// 18.5.13.1: when the soft constraints do not contradict one another (or the
// hard constraints), the result is the same as if every constraint were
// declared hard. The two soft preferences x == 5 and y == 7 are jointly
// satisfiable, so both are honored exactly as hard equalities would be.
TEST(SoftConstraintPriority, NonContradictingSoftConstraintsAllHonored) {
  ConstraintSolver solver(55);
  AddRand(solver, "x", 0, 100);
  AddRand(solver, "y", 0, 100);

  ConstraintBlock block;
  block.name = "c_soft";
  ConstraintExpr ix, sx;
  MakeSoftEq(ix, sx, "x", 5);
  block.constraints.push_back(sx);
  ConstraintExpr iy, sy;
  MakeSoftEq(iy, sy, "y", 7);
  block.constraints.push_back(sy);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  EXPECT_EQ(solver.GetValue("x"), 5);
  EXPECT_EQ(solver.GetValue("y"), 7);
}

}  // namespace
