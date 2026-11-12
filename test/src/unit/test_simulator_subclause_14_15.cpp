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

TEST(ClockvarEventSim, EdgeAndMixedEdgeEventsWakeOnTheSampledChange) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  logic clk = 0;\n"
          "  logic s1 = 1, x = 0, y = 0;\n"
          "  int e1, e2, np, xy;\n"
          "  always #5 clk = ~clk;\n"
          "  clocking cb @(posedge clk);\n"
          "    input s1, x, y;\n"
          "  endclocking\n"
          "  initial begin #7 s1 = 0; #11 y = 1; #9 s1 = 1; end\n"
          "  initial begin @(edge cb.s1) e1 = $time; @(edge cb.s1) e2 = $time; "
          "end\n"
          "  initial begin @(negedge cb.s1 or posedge cb.s1) np = $time; end\n"
          "  initial begin @(negedge cb.x or posedge cb.y) xy = $time; end\n"
          "  initial #40 begin $display(\"%0d %0d %0d %0d\", e1, e2, np, xy); "
          "$finish; end\n"
          "endmodule\n",
          f),
      "15 35 15 25\n$finish at time 40\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClockvarEventSim,
     DISABLED_ASelectsDynamicIndexIsEvaluatedOnceWhenTheWaitStarts) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  logic clk = 0;\n"
          "  logic [7:0] p = 0, n = 8'hff, e = 0, c = 0, w = 0, u = 0, v = 0, "
          "r = 0;\n"
          "  int ip = 0, in = 0, ie = 0, ic = 0, iw = 0, iu = 0, iv = 0, ir = "
          "0;\n"
          "  int tp, tn, te, tc, tw, tuv, tq, ta;\n"
          "  always #5 clk = ~clk;\n"
          "  clocking cb @(posedge clk);\n"
          "    input p, n, e, c, w, u, v;\n"
          "    inout q = r;\n"
          "  endclocking\n"
          "  initial begin\n"
          "    #1 ip = 1; in = 1; ie = 1; ic = 1; iw = 4; iu = 1; iv = 1; ir = "
          "1;\n"
          "    #11 p[1] = 1; n[1] = 0; e[1] = 1; c[1] = 1; w[5:4] = 3; u[1] = "
          "1; r[1] = 1;\n"
          "    #10 p[0] = 1; n[0] = 0; e[0] = 1; c[0] = 1; w[1:0] = 3; v[0] = "
          "1; r[0] = 1;\n"
          "  end\n"
          "  initial @(posedge cb.p[ip]) tp = $time;\n"
          "  initial @(negedge cb.n[in]) tn = $time;\n"
          "  initial @(edge cb.e[ie]) te = $time;\n"
          "  initial @(cb.c[ic]) tc = $time;\n"
          "  initial @(cb.w[iw +: 2]) tw = $time;\n"
          "  initial @(posedge cb.u[iu] or posedge cb.v[iv]) tuv = $time;\n"
          "  initial @(cb.q[ir]) tq = $time;\n"
          "  initial #2 @(posedge cb.p[ip]) ta = $time;\n"
          "  initial #40 begin\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", tp, tn, te, tc, "
          "tw, tuv, tq, ta);\n"
          "    $finish;\n"
          "  end\n"
          "endmodule\n",
          f),
      "25 25 25 25 25 25 25 15\n$finish at time 40\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
