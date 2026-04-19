#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Register a `$hold` timing check with ref = clk (timestamp event),
// data = data (timecheck event), and the given limit.
TimingCheckEntry MakeHold(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = limit;
  return tc;
}

// Window is [ref_time, ref_time + limit) = [100, 105). A timecheck
// strictly inside reports a violation.
TEST(HoldTimingCheckWindow, TimecheckStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 103));
}

// §31.3.2: only the end of the window is excluded; the beginning is
// part of the violation region. Begin endpoint = ref_time itself.
TEST(HoldTimingCheckWindow, BeginEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 100));
}

// §31.3.2: only the end of the window is excluded from the violation
// region. End endpoint = ref_time + limit.
TEST(HoldTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 105));
}

// Timecheck strictly before the ref edge is outside the window.
TEST(HoldTimingCheckWindow, TimecheckBeforeRefDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 95));
}

// Timecheck strictly after the end of the window does not violate.
TEST(HoldTimingCheckWindow, TimecheckAfterWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 110));
}

// Re-run the interior and endpoint cases at a different limit to pin
// down that the window actually scales with `limit` rather than a
// constant. With limit=3 and ref_time=100 the window is [100, 103) —
// the three integer points 100, 101, 102 violate while 103 does not.
TEST(HoldTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(3));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 99));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 100));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 101));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 102));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 103));
}

// §31.3.2: when the limit is zero, `$hold` shall never issue a
// violation. Exercise the case that would otherwise be most suspect
// (equal times at the would-be begin endpoint).
TEST(HoldTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(0));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 101));
}

// §31.3.2: a registered `$hold` entry is retrievable from the manager
// with its kind preserved.
TEST(SystemTimingCheckSim, HoldEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 5;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].kind, TimingCheckKind::kHold);
}

// §31.3.2 end-to-end: a module containing `$hold` in its specify block
// lowers and simulates; surrounding procedural code still runs.
TEST(SystemTimingCheckSim, HoldSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $hold(posedge clk, data, 5);\n"
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

}  // namespace
