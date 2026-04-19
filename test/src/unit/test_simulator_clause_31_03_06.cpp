#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Register a `$recrem` timing check with ref = clk, data = rst, and the given
// recovery / removal limits written into `limit` / `limit2` respectively —
// matching the `$recrem(ref, data, recovery_limit, removal_limit)` argument
// order from §31.3.6 Syntax 31-8.
TimingCheckEntry MakeRecrem(uint64_t recovery_limit, uint64_t removal_limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "rst";
  tc.limit = recovery_limit;
  tc.limit2 = removal_limit;
  return tc;
}

// Data event before the reference edge picks the removal-side window
// (ref_time - removal_limit, ref_time]. A timestamp strictly inside the
// interior (97 in (96, 100]) reports a violation.
TEST(RecremTimingCheckWindow, DataFirstStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 97));
}

// §31.3.6: "Only the beginning of the time window is not part of the
// violation region" for the data-event-first case. Begin = ref - removal.
TEST(RecremTimingCheckWindow, DataFirstBeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 96));
}

// §31.3.6: "$recrem check shall report a timing violation when the reference
// and data events occur simultaneously" — the end of the data-first window
// (= ref_time itself) is inclusive, so simultaneous events violate while the
// removal limit is positive.
TEST(RecremTimingCheckWindow, DataFirstEndEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
}

// A timestamp strictly before the removal window is outside the region.
TEST(RecremTimingCheckWindow, DataFirstBeforeWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 90));
}

// Data event after the reference edge picks the recovery-side window
// [ref_time, ref_time + recovery_limit). Interior violates.
TEST(RecremTimingCheckWindow, DataSecondStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 105));
}

// §31.3.6: in the data-second case "Only the end of the time window is not
// part of the violation region" — end = ref + recovery.
TEST(RecremTimingCheckWindow, DataSecondEndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 108));
}

// A timestamp strictly after the recovery window is outside the region.
TEST(RecremTimingCheckWindow, DataSecondAfterWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 115));
}

// Re-run interior and endpoint cases at different recovery and removal
// limits to pin down that each window scales with its respective limit.
// removal=3 shrinks the data-first window to (97, 100]; recovery=7 widens the
// data-second window to [100, 107).
TEST(RecremTimingCheckWindow, WindowsScaleWithLimits) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(7, 3));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 96));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 97));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 98));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 106));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 107));
}

// §31.3.6: "When both limits are zero, the $recrem check shall never issue a
// violation." Exercises the simultaneous case that would otherwise be most
// suspect.
TEST(RecremTimingCheckWindow, BothLimitsZeroNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(0, 0));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 99));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 101));
}

// Moved from A.7.5.1: a registered `$recrem` entry preserves its kind and
// both limits when retrieved from the manager.
TEST(TimingCheckCommandSim, RecremDualLimitsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "rst";
  tc.limit = 8;
  tc.limit2 = 3;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kRecrem);
  EXPECT_EQ(stored.limit, 8u);
  EXPECT_EQ(stored.limit2, 3u);
}

// §31.3.6 end-to-end: a module containing `$recrem` in its specify block
// lowers and simulates; surrounding procedural code still runs.
TEST(SystemTimingCheckSim, RecremSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3);\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §31.3.6 end-to-end: the full Syntax 31-8 invocation with notifier and the
// trailing pair of delayed signal identifiers drives elaboration and
// simulation without disturbing surrounding procedural code.
TEST(TimingCheckCommandSim, RecremFullArgsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
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
