#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SyncDriveSim, OutputDriveZeroSkewSchedulesReNBA) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* out = f.ctx.CreateVariable("out_data", 8);
  out->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "out_data";
  sig.direction = ClockingDir::kOutput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "out_data", 0xFE, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{5}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(out->value.ToUint64(), 0xFEu);
}

TEST(SyncDriveSim, OutputDriveWithNonzeroSkew) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* out = f.ctx.CreateVariable("data_out", 8);
  out->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr,
                     {"cb",
                      Edge::kPosedge,
                      {0},
                      SimTime{3},
                      "data_out",
                      ClockingDir::kOutput});

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "data_out", 0x55, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(out->value.ToUint64(), 0x55u);
}

TEST(SyncDriveSim, LastDriveWinsInSameTimestep) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* out = f.ctx.CreateVariable("nibble", 4);
  out->value = MakeLogic4VecVal(f.arena, 4, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "nibble";
  sig.direction = ClockingDir::kOutput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "nibble", 0x05, f.ctx, f.scheduler);
    cmgr.ScheduleOutputDrive("cb", "nibble", 0x03, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{5}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(out->value.ToUint64(), 0x03u);
}

TEST(SyncDriveSim, DriveRegionIsAlwaysReNBA) {
  EXPECT_EQ(SynchronousDriveRegion(), Region::kReNBA);
}

TEST(SyncDriveSim, NonCoincidentDriveDefersToNextClockingEvent) {
  SimTime now{10};
  SimTime next_event{20};
  SimTime skew{2};
  EXPECT_EQ(SynchronousDriveEffectiveTime(now, true, next_event, skew).ticks,
            uint64_t{12});
  EXPECT_EQ(SynchronousDriveEffectiveTime(now, false, next_event, skew).ticks,
            uint64_t{22});
}

TEST(SyncDriveSim, ClockvarNetDriverHasStrongStrength) {
  DriverStrength ds = ClockvarNetDriverStrength();
  EXPECT_EQ(ds.s0, Strength::kStrong);
  EXPECT_EQ(ds.s1, Strength::kStrong);
}

TEST(SyncDriveSim, ClockvarNetDriverInitIsHighZ) {
  ClockingSimFixture f;
  Logic4Vec v = MakeClockvarNetDriverInit(f.arena, 8);
  ASSERT_GT(v.nwords, 0u);
  EXPECT_FALSE(v.IsKnown());
  EXPECT_EQ(v.words[0].aval, 0u);
  EXPECT_EQ(v.words[0].bval, 0xFFu);
}

TEST(SyncDriveSim, SynchronousDriveFromSourceDrivesTheSignal) {
  SimFixture f;
  auto* sig = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic [7:0] sig = 8'h00;\n"
      "  clocking cb @(posedge clk);\n"
      "    output sig;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    cb.sig <= 8'hFE;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "sig");
  ASSERT_NE(sig, nullptr);
  EXPECT_EQ(sig->value.ToUint64(), 0xFEu);
}

TEST(SyncDriveSim, DriveToAnInputClockvarLeavesTheSignalAlone) {
  SimFixture f;
  auto* sig = RunAndFindVar(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  logic [7:0] sig = 8'h11;\n"
      "  clocking cb @(posedge clk);\n"
      "    input sig;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    #5 clk = 1'b1;\n"
      "    cb.sig <= 8'hFE;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "sig");
  ASSERT_NE(sig, nullptr);
  EXPECT_EQ(sig->value.ToUint64(), 0x11u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "write to input clockvar 'cb.sig'", 9, "14.3"));
}

TEST(SyncDriveSim, AChildInstancesClockvarDrivesThatInstancesSignal) {
  SimFixture f;
  auto* sig = RunAndFindVar(
      "module leaf(input logic clk);\n"
      "  logic [7:0] sig = 8'h00;\n"
      "  clocking cb @(posedge clk);\n"
      "    output sig;\n"
      "  endclocking\n"
      "  initial #5 cb.sig <= 8'hFE;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 1'b0;\n"
      "  leaf u(.clk(clk));\n"
      "  initial #7 clk = 1'b1;\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      f, "u.sig");
  ASSERT_NE(sig, nullptr);
  EXPECT_EQ(sig->value.ToUint64(), 0xFEu);
}

TEST(SyncDriveSim, TwoInstancesOfOneCellDriveTheirOwnSignals) {
  const char* const kSrc =
      "module leaf(input logic clk);\n"
      "  logic [7:0] sig = 8'h11;\n"
      "  clocking cb @(posedge clk);\n"
      "    output sig;\n"
      "  endclocking\n"
      "  always @(posedge clk) cb.sig <= 8'hFE;\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk1 = 1'b0;\n"
      "  logic clk2 = 1'b0;\n"
      "  leaf u1(.clk(clk1));\n"
      "  leaf u2(.clk(clk2));\n"
      "  initial begin\n"
      "    #5 clk1 = 1'b1;\n"
      "    #10 $finish;\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto* driven = RunAndFindVar(kSrc, f, "u1.sig");
  ASSERT_NE(driven, nullptr);
  EXPECT_EQ(driven->value.ToUint64(), 0xFEu);
  auto* untouched = f.ctx.FindVariable("u2.sig");
  ASSERT_NE(untouched, nullptr);
  EXPECT_EQ(untouched->value.ToUint64(), 0x11u);
}

TEST(SyncDriveSim, DriveUpdateWakesEventControlsOnTheSignal) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  logic clk = 0;\n"
                 "  logic [7:0] q = 1;\n"
                 "  clocking cb @(posedge clk);\n"
                 "    output q;\n"
                 "  endclocking\n"
                 "  always #5 clk = ~clk;\n"
                 "  always @(q) $display(\"always@q t=%0t q=%0d\", $time, q);\n"
                 "  initial begin\n"
                 "    @(q); $display(\"initial@q t=%0t q=%0d\", $time, q);\n"
                 "  end\n"
                 "  initial begin\n"
                 "    @(posedge clk);\n"
                 "    cb.q <= 9;\n"
                 "    #20 $finish;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "always@q t=5 q=9\ninitial@q t=5 q=9\n$finish at time 25\n");
}

TEST(SyncDriveSim, DriveUpdatePropagatesThroughPortAndAssign) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module dut(input logic clk, input logic [7:0] in);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  logic [7:0] din = 0;\n"
                       "  wire [7:0] w = din;\n"
                       "  clocking cb @(posedge clk);\n"
                       "    output din;\n"
                       "  endclocking\n"
                       "  always #5 clk = ~clk;\n"
                       "  dut u_dut(clk, din);\n"
                       "  initial begin\n"
                       "    @(cb); cb.din <= 55;\n"
                       "    #2 $display(\"top t=%0t din=%0d u_dut.in=%0d "
                       "w=%0d\", $time, din, u_dut.in, w);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "top t=7 din=55 u_dut.in=55 w=55\n$finish at time 7\n");
}

TEST(SyncDriveSim, ProgramDriveReachesTheDesignAtTheNextEdge) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program tb(input logic clk, output logic [7:0] din);\n"
                       "  clocking cb @(posedge clk);\n"
                       "    output din;\n"
                       "  endclocking\n"
                       "  initial begin\n"
                       "    din = 0;\n"
                       "    @(cb);\n"
                       "    cb.din <= 55;\n"
                       "    repeat (3) @(cb);\n"
                       "  end\n"
                       "endprogram\n"
                       "module dut(input logic clk, input logic [7:0] in);\n"
                       "  always @(posedge clk) if (in == 55) begin\n"
                       "    $display(\"dut t=%0t in=%0d\", $time, in);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  logic [7:0] din;\n"
                       "  always #5 clk = ~clk;\n"
                       "  tb u_tb(clk, din);\n"
                       "  dut u_dut(clk, din);\n"
                       "  initial #40 $finish;\n"
                       "endmodule\n",
                       f),
            "dut t=15 in=55\n$finish at time 15\n");
}

TEST(SyncDriveSim, DriveWithACycleDelayMaturesThatManyCyclesLater) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  logic [7:0] v = 1, w = 0, r = 5;\n"
                       "  default clocking cb @(posedge clk);\n"
                       "    output v, w;\n"
                       "  endclocking\n"
                       "  always #5 clk = ~clk;\n"
                       "  initial begin @(cb); cb.v <= ##2 r; r = 6; end\n"
                       "  initial begin\n"
                       "    ##1; cb.w <= 1; cb.w <= ##2 3; ##1 cb.w <= 2;\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #6 $write(\"%0d %0d \", v, w);\n"
                       "    #10 $write(\"%0d %0d \", v, w);\n"
                       "    #10 $display(\"%0d %0d\", v, w);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1 1 2 5 3\n$finish at time 26\n");
}

TEST(SyncDriveSim, DriveToABitSelectOrSliceOfAClockvar) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  logic [7:0] q = 8'b00000000;\n"
                       "  int i = 2;\n"
                       "  clocking cb @(posedge clk);\n"
                       "    output q;\n"
                       "  endclocking\n"
                       "  always #5 clk = ~clk;\n"
                       "  initial begin\n"
                       "    @(cb);\n"
                       "    cb.q[i] <= 1'b1;\n"
                       "    cb.q[7:4] <= 4'b1010;\n"
                       "    cb.q[1:0] <= ##1 2'b11;\n"
                       "    i = 0;\n"
                       "    #1 $write(\"%b \", q);\n"
                       "    #10 $display(\"%b\", q);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "10100100 10100111\n$finish at time 16\n");
}

TEST(SyncDriveSim, DriveBetweenClockingEventsMaturesAtTheNextEvent) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic clk = 0;\n"
                       "  logic [7:0] v = 0, r = 5;\n"
                       "  default clocking cb @(posedge clk);\n"
                       "    output v;\n"
                       "  endclocking\n"
                       "  always #5 clk = ~clk;\n"
                       "  initial begin\n"
                       "    #3 cb.v <= r;\n"
                       "    r = 6;\n"
                       "    #1 $write(\"%0d \", v);\n"
                       "    #2 $display(\"%0d\", v);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 5\n$finish at time 6\n");
}

}  // namespace
