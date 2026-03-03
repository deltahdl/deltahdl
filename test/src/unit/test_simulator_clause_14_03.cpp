// §14.3: Clocking block declaration

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// Simulation tests — A.6.11 Clocking block
// =============================================================================
// --- clocking_declaration: register and find ---
TEST(SimA611, RegisterClockingBlock) {
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

// --- default_skew: default skew applied to signals ---
TEST(SimA611, DefaultSkewApplied) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{3};
  block.default_output_skew = SimTime{5};

  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "data").ticks, 3u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "other").ticks, 5u);
}

// --- clocking_direction: inout signal has both input and output skew ---
TEST(SimA611, InoutSignalSkew) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{2};
  block.default_output_skew = SimTime{4};

  ClockingSignal sig;
  sig.signal_name = "bidir";
  sig.direction = ClockingDir::kInout;
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "bidir").ticks, 2u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "bidir").ticks, 4u);
}

// --- multiple clocking blocks ---
TEST(SimA611, MultipleClockingBlocks) {
  ClockingManager cmgr;

  ClockingBlock b1;
  b1.name = "cb_fast";
  b1.clock_signal = "fast_clk";
  b1.clock_edge = Edge::kPosedge;
  b1.default_input_skew = SimTime{1};
  b1.default_output_skew = SimTime{1};
  cmgr.Register(b1);

  ClockingBlock b2;
  b2.name = "cb_slow";
  b2.clock_signal = "slow_clk";
  b2.clock_edge = Edge::kNegedge;
  b2.default_input_skew = SimTime{5};
  b2.default_output_skew = SimTime{5};
  cmgr.Register(b2);

  EXPECT_EQ(cmgr.Count(), 2u);
  EXPECT_NE(cmgr.Find("cb_fast"), nullptr);
  EXPECT_NE(cmgr.Find("cb_slow"), nullptr);
}

// Helper fixture for clocking simulation tests.
// Schedule posedge at a given time through the scheduler.
// Schedule negedge at a given time through the scheduler.
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

// =============================================================================
// ClockingBlock registration
// =============================================================================
TEST(Clocking, RegisterAndFind) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb_main";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{2};
  block.default_output_skew = SimTime{3};

  mgr.Register(block);
  EXPECT_EQ(mgr.Count(), 1u);

  const auto* found = mgr.Find("cb_main");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->clock_signal, "clk");
  EXPECT_EQ(found->default_input_skew.ticks, 2u);
}

TEST(Clocking, FindNonexistent) {
  ClockingManager mgr;
  EXPECT_EQ(mgr.Find("nonexistent"), nullptr);
}

// =============================================================================
// 4. Default clocking skew (S14.5)
// =============================================================================
TEST(ClockingSim, DefaultSkewAppliedToAllSignals) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{3};
  block.default_output_skew = SimTime{7};

  ClockingSignal in_sig;
  in_sig.signal_name = "a";
  in_sig.direction = ClockingDir::kInput;
  block.signals.push_back(in_sig);

  ClockingSignal out_sig;
  out_sig.signal_name = "b";
  out_sig.direction = ClockingDir::kOutput;
  block.signals.push_back(out_sig);

  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetInputSkew("cb", "a").ticks, 3u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "b").ticks, 7u);
}

}  // namespace
