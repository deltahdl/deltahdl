// §31.4.4: $width


#include "simulation/lowerer.h"
#include "simulation/specify.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 Runtime — $width threshold is second limit
// =============================================================================
TEST(SimA70501, WidthThresholdAsLimit2) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.limit2 = 1;  // threshold
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kWidth);
  EXPECT_EQ(stored.limit, 20u);
  EXPECT_EQ(stored.limit2, 1u);
}

}  // namespace
