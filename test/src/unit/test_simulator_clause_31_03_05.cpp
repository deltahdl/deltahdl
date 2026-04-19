#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Register a `$recovery` timing check with ref = rst (timestamp event),
// data = clk (timecheck event), and the given limit.
TimingCheckEntry MakeRecovery(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecovery;
  tc.ref_signal = "rst";
  tc.data_signal = "clk";
  tc.limit = limit;
  return tc;
}

// Window is [ref_time, ref_time + limit) = [100, 105). A timecheck
// strictly inside reports a violation.
TEST(RecoveryTimingCheckWindow, TimecheckStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 103));
}

// §31.3.5: only the end of the window is excluded; the beginning is
// part of the violation region. Begin endpoint = ref_time itself.
TEST(RecoveryTimingCheckWindow, BeginEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 100));
}

// §31.3.5: only the end of the window is excluded from the violation
// region. End endpoint = ref_time + limit.
TEST(RecoveryTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 105));
}

// Timecheck strictly before the ref edge is outside the window.
TEST(RecoveryTimingCheckWindow, TimecheckBeforeRefDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 95));
}

// Timecheck strictly after the end of the window does not violate.
TEST(RecoveryTimingCheckWindow, TimecheckAfterWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 110));
}

// Re-run the interior and endpoint cases at a different limit to pin
// down that the window actually scales with `limit` rather than a
// constant. With limit=3 and ref_time=100 the window is [100, 103) —
// the three integer points 100, 101, 102 violate while 103 does not.
TEST(RecoveryTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(3));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 99));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 100));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 101));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 102));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 103));
}

// §31.3.5: when the limit is zero, `$recovery` shall never issue a
// violation. Exercise the case that would otherwise be most suspect
// (equal times at the would-be begin endpoint).
TEST(RecoveryTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(0));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 100));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 99));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 101));
}

// §31.3.5 end-to-end: a module containing `$recovery` in its specify block
// lowers and simulates; surrounding procedural code still runs.
TEST(SystemTimingCheckSim, RecoverySimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recovery(posedge rst, posedge clk, 5);\n"
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
