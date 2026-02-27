// §31.2: Overview


#include "simulation/lowerer.h"
#include "simulation/specify.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// All 12 kinds can be stored in SpecifyManager
TEST(SimA705, RuntimeAllTwelveKinds) {
  SpecifyManager mgr;
  TimingCheckKind kinds[] = {
      TimingCheckKind::kSetup,     TimingCheckKind::kHold,
      TimingCheckKind::kSetuphold, TimingCheckKind::kRecovery,
      TimingCheckKind::kRemoval,   TimingCheckKind::kRecrem,
      TimingCheckKind::kSkew,      TimingCheckKind::kTimeskew,
      TimingCheckKind::kFullskew,  TimingCheckKind::kPeriod,
      TimingCheckKind::kWidth,     TimingCheckKind::kNochange,
  };
  for (auto kind : kinds) {
    TimingCheckEntry tc;
    tc.kind = kind;
    tc.ref_signal = "clk";
    tc.data_signal = "data";
    tc.limit = 10;
    mgr.AddTimingCheck(tc);
  }
  EXPECT_EQ(mgr.TimingCheckCount(), 12u);
  for (uint32_t i = 0; i < 12; ++i) {
    EXPECT_EQ(mgr.GetTimingChecks()[i].kind, kinds[i]);
  }
}

}  // namespace
