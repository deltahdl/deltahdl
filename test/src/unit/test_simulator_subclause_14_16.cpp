#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "simulator/clocking.h"
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

// §14.16: a synchronous drive schedules its new value in the Re-NBA region
// whether or not there is skew or a cycle delay; only the target time step
// differs. This is the region ScheduleOutputDrive uses for every drive.
TEST(SyncDriveSim, DriveRegionIsAlwaysReNBA) {
  EXPECT_EQ(SynchronousDriveRegion(), Region::kReNBA);
}

// §14.16: a drive that runs coincident with its clocking event takes effect at
// that event (plus skew); a drive that runs at any other time performs its
// action as if it had run at the next clocking event (plus skew). This is the
// time-placement rule ScheduleOutputDrive uses to position the drive.
TEST(SyncDriveSim, NonCoincidentDriveDefersToNextClockingEvent) {
  SimTime now{10};
  SimTime next_event{20};
  SimTime skew{2};
  EXPECT_EQ(
      SynchronousDriveEffectiveTime(now, /*event_now=*/true, next_event, skew)
          .ticks,
      uint64_t{12});
  EXPECT_EQ(
      SynchronousDriveEffectiveTime(now, /*event_now=*/false, next_event, skew)
          .ticks,
      uint64_t{22});
}

// §14.16: the implicit driver created on a net target has (strong1, strong0)
// drive strength.
TEST(SyncDriveSim, ClockvarNetDriverHasStrongStrength) {
  DriverStrength ds = ClockvarNetDriverStrength();
  EXPECT_EQ(ds.s0, Strength::kStrong);
  EXPECT_EQ(ds.s1, Strength::kStrong);
}

// §14.16: that implicit net driver is initialized to 'z, so it does not
// influence its target net until a synchronous drive occurs.
TEST(SyncDriveSim, ClockvarNetDriverInitIsHighZ) {
  ClockingSimFixture f;
  Logic4Vec v = MakeClockvarNetDriverInit(f.arena, 8);
  ASSERT_GT(v.nwords, 0u);
  EXPECT_FALSE(v.IsKnown());
  EXPECT_EQ(v.words[0].aval, 0u);
  EXPECT_EQ(v.words[0].bval, 0xFFu);
}

// §14.16: "Clocking block outputs (output or inout) are used to drive values
// onto their corresponding signals, but at a specified time." The cases above
// drive the primitive from C++ on a ClockingManager they build themselves,
// which says nothing about whether a design's `cb.sig <= 8'hFE;` reaches it.
// This one starts from source: the block is declared, the drive is written as
// §14.16 spells it, and the signal is read afterwards.
//
// sig is seeded to 8'h00 and driven to 8'hFE, so the value read back can only
// have come from the drive.
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

// §14.16 makes the drive a property of the block's outputs: a clocking block
// input "is used to sample" its signal and is not a drive target. A design
// writing the same statement against an input clockvar must therefore leave the
// signal alone, which is what separates the recognition above from one that
// drives whatever member it is handed.
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
}

// §14.16's synchronous drive, written against a block a child instance
// declares. The clockvar names the block by the bare name the child's module
// declared, and the signal it drives is the child instance's own.
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
      "  initial #10 $finish;\n"
      "endmodule\n",
      f, "u.sig");
  ASSERT_NE(sig, nullptr);
  EXPECT_EQ(sig->value.ToUint64(), 0xFEu);
}

// §14.3 names a block within its module, so two instances of one module declare
// two blocks spelled identically and each drives its own signal. Only `u1`'s
// clock rises here, so `u1` drives and `u2` keeps the value its declaration
// gave it; a single registration shared between the instances would put one
// instance's drive on whichever signal that registration named.
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

}  // namespace
