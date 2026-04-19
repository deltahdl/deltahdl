#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// §31.9.2: with a positive setup and positive hold, both the setup-like
// and hold-like decomposed checks are active, so a single timestamp
// condition gates both first-to-transition sides (data for the setup
// portion, reference for the hold portion).
TEST(NegativeTimingConditionRoles, TimestampBothNonNegativeIsBoth) {
  EXPECT_EQ(TimestampConditionRole(/*setup=*/5, /*hold=*/10),
            NegativeTimingConditionRole::kBoth);
}

// §31.9.2: symmetrically, the timecheck condition gates the
// second-to-transition side of both decomposed checks when setup and
// hold are both non-negative.
TEST(NegativeTimingConditionRoles, TimecheckBothNonNegativeIsBoth) {
  EXPECT_EQ(TimecheckConditionRole(/*setup=*/5, /*hold=*/10),
            NegativeTimingConditionRole::kBoth);
}

// §31.9.2: zero is non-negative on both sides and must behave the same
// as strictly-positive — the equivalence in the LRM does not carve out
// exact-zero edges.
TEST(NegativeTimingConditionRoles, BothZeroIsBoth) {
  EXPECT_EQ(TimestampConditionRole(0, 0), NegativeTimingConditionRole::kBoth);
  EXPECT_EQ(TimecheckConditionRole(0, 0), NegativeTimingConditionRole::kBoth);
}

// §31.9.2: a negative setup with non-negative hold shifts the window
// entirely after the reference edge. The reference transitions first
// (timestamp = ref) and data transitions second (timecheck = data).
TEST(NegativeTimingConditionRoles, NegativeSetupTimestampIsRef) {
  EXPECT_EQ(TimestampConditionRole(/*setup=*/-10, /*hold=*/20),
            NegativeTimingConditionRole::kRef);
}

// §31.9.2 example 1 on page 922: `$setuphold(posedge CP, D, -10, 20,
// notifier, ,TE_cond_D, ...)` — the timecheck condition is associated
// with the data signal because the negative setup makes data the
// second-to-transition delayed signal.
TEST(NegativeTimingConditionRoles, NegativeSetupTimecheckIsData) {
  EXPECT_EQ(TimecheckConditionRole(/*setup=*/-10, /*hold=*/20),
            NegativeTimingConditionRole::kData);
}

// §31.9.2: a negative hold with non-negative setup shifts the window
// entirely before the reference edge. Data transitions first
// (timestamp = data) and reference transitions second (timecheck = ref).
TEST(NegativeTimingConditionRoles, NegativeHoldTimestampIsData) {
  EXPECT_EQ(TimestampConditionRole(/*setup=*/20, /*hold=*/-10),
            NegativeTimingConditionRole::kData);
}

// §31.9.2 example 2 on page 922: `$setuphold(posedge CP, TI, 20, -10,
// notifier, ,TE_cond_TI, ...)` — the timecheck condition is associated
// with the reference signal because the negative hold makes the
// reference the second-to-transition delayed signal.
TEST(NegativeTimingConditionRoles, NegativeHoldTimecheckIsRef) {
  EXPECT_EQ(TimecheckConditionRole(/*setup=*/20, /*hold=*/-10),
            NegativeTimingConditionRole::kRef);
}

// §31.9.2 via §31.9.1: a configuration with both setup and hold negative
// is mutually inconsistent and the §31.9.1 resolver must rewrite one of
// the limits to zero before the condition roles are defined. The helper
// surfaces the pre-resolution case as kNone so callers do not silently
// pick an arbitrary side.
TEST(NegativeTimingConditionRoles, BothNegativeIsNone) {
  EXPECT_EQ(TimestampConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
  EXPECT_EQ(TimecheckConditionRole(-1, -1), NegativeTimingConditionRole::kNone);
}

// §31.9.2: once the resolver collapses the smaller-magnitude negative
// to zero, a remaining negative setup paired with zero hold behaves
// exactly like the negative-setup-with-positive-hold case — the window
// still sits at or after the reference edge.
TEST(NegativeTimingConditionRoles, NegativeSetupZeroHoldMatchesNegativeSetup) {
  EXPECT_EQ(TimestampConditionRole(/*setup=*/-5, /*hold=*/0),
            NegativeTimingConditionRole::kRef);
  EXPECT_EQ(TimecheckConditionRole(/*setup=*/-5, /*hold=*/0),
            NegativeTimingConditionRole::kData);
}

// §31.9.2: symmetrically, a zero setup paired with a negative hold
// keeps the window at or before the reference edge.
TEST(NegativeTimingConditionRoles, ZeroSetupNegativeHoldMatchesNegativeHold) {
  EXPECT_EQ(TimestampConditionRole(/*setup=*/0, /*hold=*/-5),
            NegativeTimingConditionRole::kData);
  EXPECT_EQ(TimecheckConditionRole(/*setup=*/0, /*hold=*/-5),
            NegativeTimingConditionRole::kRef);
}

// §31.9.2: an end-to-end smoke check that a $setuphold invocation
// carrying both post-notifier condition arguments flows through
// lowering and scheduler execution without perturbing unrelated state.
TEST(NegativeTimingConditions, SetupholdBothConditionsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// §31.9.2 via §31.9's identical-behaviour rule: the $recrem simulator
// path must accept the same post-notifier condition pair that
// $setuphold does, so the negative-hold recovery/removal decomposition
// can attach conditions to the correct delayed signal at runtime.
TEST(NegativeTimingConditions, RecremBothConditionsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "  initial x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}  // namespace
