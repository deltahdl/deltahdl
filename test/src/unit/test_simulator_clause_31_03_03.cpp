// §31.3.3: $setuphold

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 Runtime — $setuphold dual limits stored in TimingCheckEntry
// =============================================================================
TEST(SimA70501, SetupholdDualLimitsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  tc.limit2 = 5;
  tc.notifier = "ntfr";
  mgr.AddTimingCheck(tc);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(stored.limit, 10u);
  EXPECT_EQ(stored.limit2, 5u);
  EXPECT_EQ(stored.notifier, "ntfr");
}

// =============================================================================
// A.7.5.1 End-to-end — $setuphold with extended args simulates
// =============================================================================
TEST(SimA70501, SetupholdFullArgsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dDATA);\n"
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
