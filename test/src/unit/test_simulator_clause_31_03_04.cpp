#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Register a `$removal` timing check with ref = rst (timecheck event),
// data = clk (timestamp event), and the given limit.
TimingCheckEntry MakeRemoval(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRemoval;
  tc.ref_signal = "rst";
  tc.data_signal = "clk";
  tc.limit = limit;
  return tc;
}

// Window is (timecheck - limit, timecheck) = (90, 100). A timestamp strictly
// inside reports a violation.
TEST(RemovalTimingCheckWindow, TimestampStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_TRUE(mgr.CheckRemovalViolation("rst", 100, "clk", 95));
}

// §31.3.4: the end points of the time window are not part of the violation
// region. Begin endpoint = timecheck - limit.
TEST(RemovalTimingCheckWindow, BeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 90));
}

// §31.3.4: the end points of the time window are not part of the violation
// region. End endpoint = timecheck time itself.
TEST(RemovalTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 100));
}

// Timestamp strictly before the window (earlier than begin) is outside and
// does not violate.
TEST(RemovalTimingCheckWindow, TimestampBeforeWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 85));
}

// Timestamp strictly after the timecheck is outside the window.
TEST(RemovalTimingCheckWindow, TimestampAfterTimecheckDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 105));
}

// Re-run the interior and endpoint cases at a different limit to pin down
// that the window actually scales with `limit` rather than a constant.
// With limit=3 and timecheck=100, begin shifts to 97 and the interior holds
// exactly two integer points (98 and 99).
TEST(RemovalTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(3));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 96));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 97));
  EXPECT_TRUE(mgr.CheckRemovalViolation("rst", 100, "clk", 98));
  EXPECT_TRUE(mgr.CheckRemovalViolation("rst", 100, "clk", 99));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 100));
}

// §31.3.4: when the limit is zero, `$removal` shall never issue a violation.
// Exercise the case that would otherwise be most suspect (equal times).
TEST(RemovalTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(0));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 100));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 99));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 101));
}

// §31.3.4 end-to-end: a module containing `$removal` in its specify block
// lowers and simulates; surrounding procedural code still runs.
TEST(SystemTimingCheckSim, RemovalSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $removal(posedge rst, posedge clk, 5);\n"
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
