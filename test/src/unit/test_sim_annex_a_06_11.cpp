#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/clocking.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

struct SimA611Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

void SchedulePosedge(SimA611Fixture &f, Variable *clk, uint64_t time) {
  auto *ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

void ScheduleNegedge(SimA611Fixture &f, Variable *clk, uint64_t time) {
  auto *ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

}  // namespace

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

  const auto *found = cmgr.Find("cb");
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

// --- clocking_direction: input sampling on posedge ---

TEST(SimA611, InputSamplingPosedge) {
  SimA611Fixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto *data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "data_in";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data_in"), 0xABu);
}

// --- clocking_direction: output driving with skew ---

TEST(SimA611, OutputDrivingWithSkew) {
  SimA611Fixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto *out = f.ctx.CreateVariable("data_out", 8);
  out->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{3};

  ClockingSignal sig;
  sig.signal_name = "data_out";
  sig.direction = ClockingDir::kOutput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  auto *ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "data_out", 0x55, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(out->value.ToUint64(), 0x55u);
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

// --- clocking_declaration: default clocking ---

TEST(SimA611, DefaultClocking) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "sys_cb";
  block.clock_signal = "sys_clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{1};
  block.default_output_skew = SimTime{2};
  cmgr.Register(block);

  cmgr.SetDefaultClocking("sys_cb");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "sys_cb");
}

// --- clocking_declaration: global clocking ---

TEST(SimA611, GlobalClocking) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "gclk";
  block.clock_signal = "clk_global";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  block.is_global = true;
  cmgr.Register(block);

  cmgr.SetGlobalClocking("gclk");
  EXPECT_EQ(cmgr.GetGlobalClocking(), "gclk");
  EXPECT_TRUE(cmgr.Find("gclk")->is_global);
}

// --- clocking block event notification ---

TEST(SimA611, ClockingBlockEvent) {
  SimA611Fixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  auto *cb_event = f.ctx.CreateVariable("__cb_event", 1);
  cb_event->is_event = true;
  cmgr.SetBlockEventVar("cb", cb_event);
  cmgr.Attach(f.ctx, f.scheduler);

  bool triggered = false;
  cb_event->AddWatcher([&triggered]() {
    triggered = true;
    return true;
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();
  EXPECT_TRUE(triggered);
}

// --- edge callback registration ---

TEST(SimA611, EdgeCallbackPosedge) {
  SimA611Fixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  uint32_t count = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&count]() { count++; });
  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  ScheduleNegedge(f, clk, 15);
  SchedulePosedge(f, clk, 20);
  f.scheduler.Run();

  EXPECT_EQ(count, 2u);
}

// --- negedge clocking block ---

TEST(SimA611, NegedgeClockEvent) {
  SimA611Fixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto *data = f.ctx.CreateVariable("neg_data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xDD);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb_neg";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kNegedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "neg_data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  ScheduleNegedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb_neg", "neg_data"), 0xDDu);
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

// --- sampled value updates across edges ---

TEST(SimA611, SampledValueUpdatesAcrossEdges) {
  SimA611Fixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto *data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  // First posedge at t=10 samples 0x11
  SchedulePosedge(f, clk, 10);

  // Change data at t=12
  auto *ev_data = f.scheduler.GetEventPool().Acquire();
  ev_data->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  };
  f.scheduler.ScheduleEvent(SimTime{12}, Region::kActive, ev_data);

  // Negedge at t=15
  ScheduleNegedge(f, clk, 15);

  // Second posedge at t=20 samples 0x22
  SchedulePosedge(f, clk, 20);

  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x22u);
}
