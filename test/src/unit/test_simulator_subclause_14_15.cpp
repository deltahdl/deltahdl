#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SyncEventSim, SampledValueUsedInSyncContext) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAA);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  uint64_t sampled_at_event = 0;
  uint64_t live_at_event = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
    sampled_at_event = cmgr.GetSampledValue("cb", "data");
    live_at_event = data->value.ToUint64();
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(sampled_at_event, 0xAAu);
  EXPECT_EQ(live_at_event, 0xFFu);
  EXPECT_NE(sampled_at_event, live_at_event);
}

TEST(SyncEventSim, ResolveClockingMemberVariable) {
  ClockingSimFixture f;

  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x55);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);

  auto* resolved = cmgr.ResolveClockingMember("cb", "data", f.ctx);
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->value.ToUint64(), 0x55u);
}

TEST(SyncEventSim, ResolveClockingMemberUnknownBlock) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  auto* resolved = cmgr.ResolveClockingMember("nonexistent", "data", f.ctx);
  EXPECT_EQ(resolved, nullptr);
}

TEST(SyncEventSim, ResolveClockingMemberUnknownSignal) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  cmgr.Register(block);

  auto* resolved = cmgr.ResolveClockingMember("cb", "nonexistent", f.ctx);
  EXPECT_EQ(resolved, nullptr);
}

TEST(SyncEventSim, SlicedClockingInputUsesSynchronousBitAtFixedIndex) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* sign = f.ctx.CreateVariable("sign", 4);
  sign->value = MakeLogic4VecVal(f.arena, 4, 0b1010);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"dom", Edge::kNegedge, {0}, {0}, "sign", ClockingDir::kInput});

  const uint32_t kCapturedIndex = 1;

  SchedulePosedge(f, clk, 5);
  ScheduleNegedge(f, clk, 10);
  f.scheduler.Run();

  uint64_t snapshot = cmgr.GetSampledValue("dom", "sign");
  uint64_t sync_bit = (snapshot >> kCapturedIndex) & 1;

  sign->value = MakeLogic4VecVal(f.arena, 4, 0b0000);
  const uint32_t kReindexed = 3;

  EXPECT_EQ(cmgr.GetSampledValue("dom", "sign"), 0b1010u);
  EXPECT_EQ(sync_bit, 1u);
  uint64_t live_reindexed_bit = (sign->value.ToUint64() >> kReindexed) & 1;
  EXPECT_NE(sync_bit, live_reindexed_bit);
}

TEST(SyncEventSim, ResolveClockingMemberMissingBackingVariable) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);

  auto* resolved = cmgr.ResolveClockingMember("cb", "data", f.ctx);
  EXPECT_EQ(resolved, nullptr);
}

TEST(SyncEventSim, InoutClockingSignalSampledAsSynchronousValue) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x3C);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInout});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x3Cu);
}

TEST(SyncEventSim, OutputClockingSignalHasNoSynchronousValue) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x55);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kOutput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0u);
}

TEST(ClockvarEventSim, EventControlOnAClockvarWakesAtItsSample) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] d = 1, b = 1;\n"
      "  logic en = 0, a = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input d, en, a, b;\n"
      "  endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin #7 d = 2; en = 1; #1 en = 0; #4 b = 9; #6 en = 1; end\n"
      "  initial begin @(cb.d); $write(\"%0t:%0d \", $time, cb.d); end\n"
      "  initial begin @(posedge cb.a or cb.b); $write(\"%0t:%0d \", $time, "
      "cb.b); end\n"
      "  initial begin\n"
      "    @(posedge cb.en); $display(\"%0t\", $time);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "15:2 15:9 25\n$finish at time 25\n");
}

}  // namespace
