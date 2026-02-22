// §14.4: Input and output skews

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulation/clocking.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>

using namespace delta;

namespace {

// =============================================================================
// Skew resolution
// =============================================================================
TEST(Clocking, DefaultInputSkew) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{5};
  block.default_output_skew = SimTime{10};
  mgr.Register(block);

  // No per-signal skew, should return default.
  auto skew = mgr.GetInputSkew("cb", "data_in");
  EXPECT_EQ(skew.ticks, 5u);
}

TEST(Clocking, PerSignalSkewOverridesDefault) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{5};
  block.default_output_skew = SimTime{10};

  ClockingSignal sig;
  sig.signal_name = "data_in";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{7};
  block.signals.push_back(sig);

  mgr.Register(block);

  auto skew = mgr.GetInputSkew("cb", "data_in");
  EXPECT_EQ(skew.ticks, 7u);

  // Unknown signal falls back to default.
  auto default_skew = mgr.GetInputSkew("cb", "other_signal");
  EXPECT_EQ(default_skew.ticks, 5u);
}

TEST(Clocking, OutputSkew) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{1};
  block.default_output_skew = SimTime{3};
  mgr.Register(block);

  auto skew = mgr.GetOutputSkew("cb", "data_out");
  EXPECT_EQ(skew.ticks, 3u);
}

} // namespace
