// §14.4: Input and output skews

#include <cstdint>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"
#include "helpers_clocking.h"

using namespace delta;

namespace {

// --- clocking_skew: per-signal skew overrides default ---
TEST(SimA611, PerSignalSkewOverride) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{10};
  block.default_output_skew = SimTime{10};

  ClockingSignal sig;
  sig.signal_name = "fast_in";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{2};
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "fast_in").ticks, 2u);
  EXPECT_EQ(cmgr.GetInputSkew("cb", "other").ticks, 10u);
}

}  // namespace
