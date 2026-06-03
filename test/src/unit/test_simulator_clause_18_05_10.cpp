#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <string>

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

// A constraint 'x > 5', which is unsatisfiable for a variable confined to
// [0, 3]: when the enclosing block is enabled the solve must fail, and when the
// block is disabled the solve can succeed. This makes a block's on/off state
// directly observable through the outcome of Solve().
ConstraintExpr XGreaterThanFive() {
  ConstraintExpr c;
  c.kind = ConstraintKind::kGreaterThan;
  c.var_name = "x";
  c.lo = 5;
  return c;
}

// Build a solver holding x in [0, 3] and one constraint block 'c' carrying the
// unsatisfiable 'x > 5'. When 'shared' is non-null the block is static and binds
// its on/off state to that shared cell, modelling one instance of the class.
ConstraintSolver MakeInstance(uint32_t seed, std::shared_ptr<bool> shared) {
  ConstraintSolver solver(seed);
  solver.AddVariable(MakeVar("x", 0, 3));
  ConstraintBlock blk;
  blk.name = "c";
  blk.constraints.push_back(XGreaterThanFive());
  if (shared) {
    blk.is_static = true;
    blk.shared_enabled = shared;
    blk.enabled = *shared;
  }
  solver.AddConstraintBlock(blk);
  return solver;
}

// 18.5.10: a constraint_mode() call on a static constraint affects all instances
// of the class. Model two instances whose static block 'c' shares one on/off
// cell: turning the constraint off through one instance is observed by the other
// — its enabled state, reported by constraint_mode() with no argument, reads as
// off without any call of its own.
TEST(StaticConstraintMode, StaticConstraintModeIsSharedAcrossInstances) {
  auto shared = std::make_shared<bool>(true);
  ConstraintSolver inst_a = MakeInstance(11, shared);
  ConstraintSolver inst_b = MakeInstance(22, shared);

  // Both start enabled: the unsatisfiable constraint blocks each instance.
  EXPECT_TRUE(inst_a.GetConstraintMode("c"));
  EXPECT_TRUE(inst_b.GetConstraintMode("c"));

  // Disabling the static constraint through one instance turns it off for the
  // other as well.
  inst_a.SetConstraintMode("c", false);
  EXPECT_FALSE(inst_b.GetConstraintMode("c"));
}

// 18.5.10: the shared on/off state governs solving, not just reporting. After
// the constraint is turned off through one instance, the other instance solves
// successfully because the (now disabled) unsatisfiable constraint no longer
// applies to it.
TEST(StaticConstraintMode, DisablingStaticConstraintFreesOtherInstanceSolve) {
  auto shared = std::make_shared<bool>(true);
  ConstraintSolver inst_a = MakeInstance(11, shared);
  ConstraintSolver inst_b = MakeInstance(22, shared);

  // While enabled, the unsatisfiable constraint makes the solve fail.
  EXPECT_FALSE(inst_b.Solve());

  // Turn it off through the first instance; the second now finds a value.
  inst_a.SetConstraintMode("c", false);
  EXPECT_TRUE(inst_b.Solve());
}

// 18.5.10: re-enabling the static constraint through one instance restores it
// for every instance, so the previously freed solve fails again.
TEST(StaticConstraintMode, ReenablingStaticConstraintAffectsOtherInstance) {
  auto shared = std::make_shared<bool>(true);
  ConstraintSolver inst_a = MakeInstance(11, shared);
  ConstraintSolver inst_b = MakeInstance(22, shared);

  inst_a.SetConstraintMode("c", false);
  EXPECT_TRUE(inst_b.Solve());

  inst_a.SetConstraintMode("c", true);
  EXPECT_FALSE(inst_b.Solve());
}

// 18.5.10: the shared on/off state governs the no-argument checker as well as
// generation. Pin x to a value the unsatisfiable constraint rejects: while the
// static constraint is on, a check of another instance fails, and once it is
// turned off through one instance the other instance's check passes because the
// disabled constraint is no longer evaluated.
TEST(StaticConstraintMode, DisablingStaticConstraintAffectsOtherInstanceCheck) {
  auto shared = std::make_shared<bool>(true);
  ConstraintSolver inst_a = MakeInstance(11, shared);
  ConstraintSolver inst_b = MakeInstance(22, shared);

  // x = 0 violates 'x > 5', so the check fails while the constraint is enabled.
  inst_b.SetValue("x", 0);
  EXPECT_FALSE(inst_b.Check());

  // Turning the static constraint off through the first instance removes it from
  // the second instance's evaluation, so the same values now check clean.
  inst_a.SetConstraintMode("c", false);
  EXPECT_TRUE(inst_b.Check());
}

// 18.5.10 (contrast): a non-static constraint's mode is per-instance. With no
// shared state, turning the constraint off through one instance leaves the
// other's copy enabled — it still reports on and its solve still fails.
TEST(StaticConstraintMode, NonStaticConstraintModeIsIndependentPerInstance) {
  ConstraintSolver inst_a = MakeInstance(11, nullptr);
  ConstraintSolver inst_b = MakeInstance(22, nullptr);

  inst_a.SetConstraintMode("c", false);

  EXPECT_TRUE(inst_b.GetConstraintMode("c"));
  EXPECT_FALSE(inst_b.Solve());
}

}  // namespace
