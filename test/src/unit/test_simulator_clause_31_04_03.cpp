// §31.4.3: $fullskew


#include "simulation/lowerer.h"
#include "simulation/specify.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 Runtime — $fullskew dual limits stored
// =============================================================================
TEST(SimA70501, FullskewDualLimitsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kFullskew;
  tc.ref_signal = "clk1";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "clk2";
  tc.data_edge = SpecifyEdge::kNegedge;
  tc.limit = 4;
  tc.limit2 = 6;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(stored.limit, 4u);
  EXPECT_EQ(stored.limit2, 6u);
}

}  // namespace
