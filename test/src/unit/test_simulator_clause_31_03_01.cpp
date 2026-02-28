// §31.3.1: $setup

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5 Runtime — TimingCheckEntry kind for each system_timing_check type
// =============================================================================
// Runtime TimingCheckEntry correctly stores each of the 12 kinds
TEST(SimA705, RuntimeTimingCheckEntrySetup) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].kind, TimingCheckKind::kSetup);
}

// =============================================================================
// A.7.5 End-to-end simulation — timing checks do not interfere
// =============================================================================
// Module with $setup timing check simulates correctly
TEST(SimA705, SetupTimingCheckSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
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

// Module with timing checks and path delays simulates correctly
TEST(SimA705, TimingChecksWithPathsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    $setup(d, posedge clk, 10);\n"
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
