// §31.3.2: $hold


#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(SimA705, RuntimeTimingCheckEntryHold) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 5;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].kind, TimingCheckKind::kHold);
}

}  // namespace
