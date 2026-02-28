// §31.3.6: $recrem

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 Runtime — $recrem dual limits stored
// =============================================================================
TEST(SimA70501, RecremDualLimitsStored) {
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

}  // namespace
