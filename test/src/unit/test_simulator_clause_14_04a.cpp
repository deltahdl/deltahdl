// Non-LRM tests

#include <cstdint>
#include <string_view>
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// 13. Per-signal skew override for input
// =============================================================================
TEST(ClockingSim, PerSignalInputSkewOverride) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{5};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "fast_in";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{1};
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "fast_in").ticks, 1u);
  EXPECT_EQ(cmgr.GetInputSkew("cb", "other").ticks, 5u);
}

// =============================================================================
// 14. Per-signal skew override for output
// =============================================================================
TEST(ClockingSim, PerSignalOutputSkewOverride) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{10};

  ClockingSignal sig;
  sig.signal_name = "fast_out";
  sig.direction = ClockingDir::kOutput;
  sig.skew = SimTime{2};
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetOutputSkew("cb", "fast_out").ticks, 2u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "other").ticks, 10u);
}

}  // namespace
