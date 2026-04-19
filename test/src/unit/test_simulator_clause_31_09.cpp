#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// Build a $setuphold entry running in §31.9 signed-limit mode with the
// supplied setup (`signed_limit`) and hold (`signed_limit2`) values.
// The unsigned `limit` / `limit2` fields are deliberately left at zero
// to confirm the runtime consults the signed fields in this mode.
TimingCheckEntry MakeSignedSetuphold(int64_t setup, int64_t hold) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = setup;
  tc.signed_limit2 = hold;
  return tc;
}

// Mirror helper for $recrem — the LRM requires the two kinds to agree
// on the signed-window semantics, so the test fixtures are deliberately
// identical except for the kind tag.
TimingCheckEntry MakeSignedRecrem(int64_t recovery, int64_t removal) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = recovery;
  tc.signed_limit2 = removal;
  return tc;
}

// §31.9: with a negative setup and positive hold the violation window
// lies entirely after the reference edge. A data transition strictly
// inside that shifted interval is a violation.
TEST(NegativeTimingChecks, NegativeSetupShiftsWindowAfterReference) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/-5, /*hold=*/10));
  // Interval is (ref+5, ref+10) — ref=100 → (105, 110).
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 107));
}

// §31.9: the reference edge itself is outside a window that does not
// straddle it, so a transition at ref_time cannot violate when setup
// is negative.
TEST(NegativeTimingChecks, NegativeSetupExcludesReferenceEdge) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/-5, /*hold=*/10));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
}

// §31.9: a transition between the reference edge and the shifted
// window's left boundary is outside the window and must not violate.
TEST(NegativeTimingChecks, NegativeSetupExcludesGapBeforeWindow) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/-5, /*hold=*/10));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 103));
}

// §31.9: with a positive setup and negative hold the window lies
// entirely before the reference edge — the mirror image of the
// negative-setup case.
TEST(NegativeTimingChecks, NegativeHoldShiftsWindowBeforeReference) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/10, /*hold=*/-3));
  // Interval is (ref-10, ref-3) — ref=100 → (90, 97).
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 94));
}

// §31.9: negative-hold counterpart — the reference edge is not inside
// the pre-edge window, so a simultaneous transition cannot violate.
TEST(NegativeTimingChecks, NegativeHoldExcludesReferenceEdge) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/10, /*hold=*/-3));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
}

// §31.9: neither window boundary is part of the violation region
// (strict inequalities at both ends). A data event landing exactly
// on the left boundary of a shifted-after window must not violate.
TEST(NegativeTimingChecks, LowerBoundaryIsExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/-5, /*hold=*/10));
  // Left boundary is ref - setup = 105.
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

// §31.9: the upper boundary is also excluded.
TEST(NegativeTimingChecks, UpperBoundaryIsExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/-5, /*hold=*/10));
  // Right boundary is ref + hold = 110.
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 110));
}

// §31.9: when both signed limits are zero the interval is empty, so
// no transition can violate regardless of when it arrives.
TEST(NegativeTimingChecks, BothSignedLimitsZeroNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/0, /*hold=*/0));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 101));
}

// §31.9: a non-negative-valued entry in signed-limit mode still
// behaves as a straddling window, matching the LRM statement that
// positive setup and hold place the window across the reference edge.
TEST(NegativeTimingChecks, PositiveSignedLimitsStraddleReference) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold(/*setup=*/10, /*hold=*/5));
  // Interval (90, 105): interior violates, reference edge violates,
  // boundaries do not.
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 94));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 103));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 90));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

// §31.9: $setuphold and $recrem must produce identical answers for
// every data time when configured with the same signed limits. The
// helper enumerates a dense set of times spanning both a shifted-
// after window and a straddling one and asserts pointwise agreement.
TEST(NegativeTimingChecks, SetupholdAndRecremAgreeForIdenticalSignedLimits) {
  struct Case {
    int64_t setup;
    int64_t hold;
  };
  const Case cases[] = {
      {-5, 10},  // window entirely after ref
      {10, -3},  // window entirely before ref
      {10, 5},   // straddling ref
      {0, 0},    // empty interval
  };
  const uint64_t ref_time = 100;
  for (const auto& c : cases) {
    SpecifyManager mgr_sh;
    SpecifyManager mgr_rr;
    mgr_sh.AddTimingCheck(MakeSignedSetuphold(c.setup, c.hold));
    mgr_rr.AddTimingCheck(MakeSignedRecrem(c.setup, c.hold));
    for (uint64_t t = 88; t <= 112; ++t) {
      const bool sh_viol =
          mgr_sh.CheckSetupholdViolation("clk", ref_time, "data", t);
      const bool rr_viol =
          mgr_rr.CheckRecremViolation("clk", ref_time, "data", t);
      EXPECT_EQ(sh_viol, rr_viol)
          << "setup=" << c.setup << " hold=" << c.hold << " t=" << t;
    }
  }
}

// §31.9: the signed-limit path is gated on `negative_timing_check_enabled`.
// An entry that leaves the flag off keeps the §31.3.3 unsigned semantics
// even if the signed fields happen to be populated — the runtime must
// not silently consume them.
TEST(NegativeTimingChecks, FlagOffPreservesUnsignedSemantics) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  tc.limit2 = 5;
  // Signed fields populated with values that would otherwise shift the
  // window entirely after the reference edge. With the flag off they
  // must be ignored.
  tc.signed_limit = -5;
  tc.signed_limit2 = 10;
  tc.negative_timing_check_enabled = false;
  mgr.AddTimingCheck(std::move(tc));
  // Baseline unsigned window is (90, 105) straddling ref=100, so a
  // transition at ref-4 must violate.
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 96));
  // And a transition at the left boundary must not.
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 90));
}

// §31.9: end-to-end acceptance of a $setuphold invocation with both
// limits negative. The parser, elaborator, lowerer, and scheduler must
// all carry the signed values through without disturbing surrounding
// procedural code — the initial-block assignment still observes its
// nominal value after the run.
TEST(NegativeTimingChecks, SetupholdNegativeLimitsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, -10, -5);\n"
      "  endspecify\n"
      "  initial x = 8'd17;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 17u);
}

// §31.9: $recrem counterpart to the $setuphold end-to-end test above.
// The LRM requires identical behaviour for the two kinds under
// negative values, so the full pipeline must accept the $recrem form
// the same way.
TEST(NegativeTimingChecks, RecremNegativeLimitsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, -8, -3);\n"
      "  endspecify\n"
      "  initial x = 8'd17;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 17u);
}

}  // namespace
