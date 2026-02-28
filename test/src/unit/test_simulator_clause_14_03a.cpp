// §14.3: Clocking block declaration

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast.h"
#include "simulation/clocking.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"
#include "helpers_clocking.h"

using namespace delta;

// Helper fixture for clocking simulation tests.
// Schedule posedge at a given time through the scheduler.

// Schedule negedge at a given time through the scheduler.

namespace {

// =============================================================================
// 1. Clocking block declaration with clock event (S14.3)
// =============================================================================
TEST(ClockingSim, DeclareWithClockEvent) {
  ClockingSimFixture f;
  ClockingManager cmgr;

  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  const auto* found = cmgr.Find("cb");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->clock_signal, "clk");
  EXPECT_EQ(found->clock_edge, Edge::kPosedge);
}

// =============================================================================
// 16. Negedge clock event
// =============================================================================
TEST(ClockingSim, NegedgeClockEvent) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  TestNegedgeSampling(f, cmgr);
}

// =============================================================================
// 17. Inout direction signal
// =============================================================================
TEST(ClockingSim, InoutSignalDirection) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{2};
  block.default_output_skew = SimTime{3};

  ClockingSignal sig;
  sig.signal_name = "bidir";
  sig.direction = ClockingDir::kInout;
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "bidir").ticks, 2u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "bidir").ticks, 3u);
}

// =============================================================================
// 20. SimContext clocking manager integration
// =============================================================================
TEST(ClockingSim, SimContextClockingManagerAccess) {
  ClockingSimFixture f;
  ClockingManager cmgr;

  ClockingBlock block;
  block.name = "main_cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  f.ctx.SetClockingManager(&cmgr);
  EXPECT_EQ(f.ctx.GetClockingManager(), &cmgr);
}

}  // namespace
