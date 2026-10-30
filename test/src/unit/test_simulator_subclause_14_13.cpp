#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(InputSamplingSim, PosedgeSamplesCurrentValue) {
  SimFixture f;
  auto [clk, data] =
      CreateClockAndSignal(f, /*clk_value=*/0, "data_in", 8, 0xAB);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data_in", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data_in"), 0xABu);
}

TEST(InputSamplingSim, NegedgeSamplesCurrentValue) {
  SimFixture f;
  ClockingManager cmgr;
  TestNegedgeSampling(f, cmgr);
}

TEST(InputSamplingSim, SampledValueUpdatesAcrossEdges) {
  SimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, /*clk_value=*/0, "data", 8, 0x11);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);

  ScheduleValueChange(f, data, 12, 0x22);

  ScheduleNegedge(f, clk, 15);

  SchedulePosedge(f, clk, 20);

  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x22u);
}

TEST(InputSamplingSim, ZeroSkewInputSamplesInObservedRegion) {
  ClockingSimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, /*clk_value=*/0, "data", 8, 0x10);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr,
                     {"cb",
                      Edge::kPosedge,
                      {0},
                      {0},
                      "data",
                      ClockingDir::kInput,
                      /*explicit_zero_skew=*/true});

  SchedulePosedge(f, clk, 10);

  ScheduleValueChange(f, data, 10, 0x20);

  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x20u);
}

// §14.13: a non-#0 (default) skew input samples the Postponed-region value from
// before the clocking event, so a same-time-step Active update to the signal
// after the edge is NOT reflected. This is the complement of the explicit-#0
// case (ZeroSkewInputSamplesInObservedRegion), which DOES observe that update
// because it samples in the Observed region after all Active events settle.
// Same stimulus, opposite result -- the only difference is
// is_explicit_zero_skew.
TEST(InputSamplingSim, NonZeroSkewInputDoesNotSampleSameStepActiveUpdate) {
  ClockingSimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, /*clk_value=*/0, "data", 8, 0x10);

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
  sig.skew = SimTime{0};
  // Default (non-explicit-#0) skew: sampled in the Active-region edge callback,
  // before the same-step data update runs.
  sig.is_explicit_zero_skew = false;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  // Clock edge scheduled first, data update second: both in the Active region
  // at t=10. The edge callback samples data before the update event fires.
  SchedulePosedge(f, clk, 10);

  ScheduleValueChange(f, data, 10, 0x20);

  f.scheduler.Run();

  // Postponed-region value from before the edge, not the same-step update.
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x10u);
}

// §14.13: a clockvar read yields the value sampled at the most recent clocking
// event, not the signal's live value. After the edge samples the signal, a
// later change to the underlying signal with no intervening clocking event
// leaves the sampled value frozen; reading cb.data through the real expression
// path still yields the old sample even though the live variable has moved on.
TEST(InputSamplingSim, ClockvarReadStaysFrozenBetweenEdges) {
  SimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, /*clk_value=*/0, "data", 8, 0xA5);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);

  // Signal changes after the edge with no further clocking event; the sample
  // must not follow it.
  ScheduleValueChange(f, data, 15, 0x3C);

  f.scheduler.Run();

  // The live variable has moved to 0x3C...
  EXPECT_EQ(data->value.ToUint64(), 0x3Cu);

  // ...but reading the clockvar through EvalExpr yields the frozen sample 0xA5.
  EXPECT_EQ(ReadClockvar(f, "cb", "data"), 0xA5u);
}

TEST(InputSamplingSim, SameSignalInMultipleBlocks) {
  ClockingSimFixture f;
  auto* clk1 = f.ctx.CreateVariable("clk1", 1);
  clk1->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* clk2 = f.ctx.CreateVariable("clk2", 1);
  clk2->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;

  ClockingBlock block1;
  block1.name = "cb1";
  block1.clock_signal = "clk1";
  block1.clock_edge = Edge::kPosedge;
  block1.default_input_skew = SimTime{0};
  block1.default_output_skew = SimTime{0};
  ClockingSignal sig1;
  sig1.signal_name = "data";
  sig1.direction = ClockingDir::kInput;
  block1.signals.push_back(sig1);
  cmgr.Register(block1);

  ClockingBlock block2;
  block2.name = "cb2";
  block2.clock_signal = "clk2";
  block2.clock_edge = Edge::kPosedge;
  block2.default_input_skew = SimTime{0};
  block2.default_output_skew = SimTime{0};
  ClockingSignal sig2;
  sig2.signal_name = "data";
  sig2.direction = ClockingDir::kInput;
  block2.signals.push_back(sig2);
  cmgr.Register(block2);

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk1, 10);

  ScheduleValueChange(f, data, 15, 0x22);

  SchedulePosedge(f, clk2, 20);

  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb1", "data"), 0x11u);
  EXPECT_EQ(cmgr.GetSampledValue("cb2", "data"), 0x22u);
}

TEST(InputSamplingSim, InoutSignalSampledAsInput) {
  SimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, /*clk_value=*/0, "data", 8, 0x55);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInout});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x55u);
}

TEST(InputSamplingSim, SampledBeforeBlockEventFires) {
  ClockingSimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, /*clk_value=*/0, "data", 8, 0x42);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  uint64_t value_seen_in_callback = 0;
  cmgr.RegisterEdgeCallback(
      "cb", f.ctx, f.scheduler, [&cmgr, &value_seen_in_callback]() {
        value_seen_in_callback = cmgr.GetSampledValue("cb", "data");
      });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(value_seen_in_callback, 0x42u);
}

// §14.13: the sampled-value rule covers inout clockvars as well as input ones
// -- reading an inout clockvar in an expression yields the value sampled at the
// most recent clocking event, just like an input clockvar. This exercises the
// inout branch of the sampler together with the real EvalExpr member-access
// read path (TryClockvarMemberAccess), the input form the input-direction
// frozen test does not cover.
TEST(InputSamplingSim, InoutClockvarReadYieldsSampledValue) {
  SimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, /*clk_value=*/0, "data", 8, 0x5A);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInout});
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(ReadClockvar(f, "cb", "data"), 0x5Au);
}

// §14.13 (printed page 366) with §6.3 and §14.16: an input clockvar reads
// its sample whole and a drive writes its value whole -- the x and z bits of
// a 4-state signal and every bit of one wider than 64. Kept as 64 known bits,
// 1x0z read as 1000, the 96-bit input lost its top word, and the drives wrote
// 0100 and the low 64 bits alone.
TEST(ClockingSampleSim, ClockvarKeepsUnknownBitsAndEveryWord) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [3:0] a = 4'b1x0z, r = 0;\n"
      "  logic [95:0] w = {32'hAAAA_BBBB, 64'h1111_2222_3333_4444}, v = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, w;\n"
      "    output r, v;\n"
      "  endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin\n"
      "    @(cb);\n"
      "    cb.r <= 4'bz1x0;\n"
      "    cb.v <= {32'hCCCC_DDDD, 64'h5555_6666_7777_8888};\n"
      "    #1 $display(\"%b %h %b %h\", cb.a, cb.w, r, v);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "1x0z aaaabbbb1111222233334444 z1x0 ccccdddd5555666677778888\n"
            "$finish at time 6\n");
}

// §14.13: an explicit #0 input is sampled in the Observed region of its
// clocking event's time step and not again when the Reactive region's writes
// run the Active, NBA and Observed regions over without a new clocking event.
// A program writes an input, an inout clockvar's signal and a 1step input
// after the event, and its write of v wakes a module process whose
// nonblocking assignment writes a fourth input; once that has run, every
// clockvar still reads what the event sampled, 0.
TEST(ClockingSampleSim, ZeroSkewInputKeepsItsSampleThroughReactiveWrites) {
  SimFixture f;
  std::string out = RunCaptureAllTops(
      "module m;\n"
      "  logic clk = 0, v = 0, w = 0, u = 0, n = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #0 v, n;\n"
      "    input #0 output w;\n"
      "    input #1step u;\n"
      "  endclocking\n"
      "  always @(v) n <= v;\n"
      "  initial #10 clk = 1;\n"
      "endmodule\n"
      "program p;\n"
      "  initial begin\n"
      "    @(m.cb);\n"
      "    m.v = 1; m.w = 1; m.u = 1;\n"
      "    wait (m.n == 1);\n"
      "    $display(\"%b%b%b%b %0t\", m.cb.v, m.cb.w, m.cb.n, m.cb.u, $time);\n"
      "  end\n"
      "endprogram\n",
      f);
  EXPECT_EQ(out, "0000 10\n");
}

// §14.13: the nearest contrast to the one above -- the program's writes make
// a new clocking event in the same time step, so the #0 input is sampled
// again and reads the 1 written, while the 1step input still reads the value
// from before the time step, 0. The new event was processed with the program
// current, and the #0 input, named from that scope, sampled nothing.
TEST(ClockingSampleSim, ZeroSkewInputResamplesOnANewEventInTheTimeStep) {
  SimFixture f;
  std::string out = RunCaptureAllTops(
      "module m;\n"
      "  logic clk = 0, v = 0, u = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #0 v;\n"
      "    input #1step u;\n"
      "  endclocking\n"
      "  initial #10 clk = 1;\n"
      "endmodule\n"
      "program p;\n"
      "  initial begin\n"
      "    @(m.cb);\n"
      "    m.v = 1; m.u = 1;\n"
      "    fork\n"
      "      begin @(m.cb); $display(\"%b%b %0t\", m.cb.v, m.cb.u, $time); "
      "end\n"
      "      begin m.clk = 0; #0 m.clk = 1; end\n"
      "    join\n"
      "  end\n"
      "endprogram\n",
      f);
  EXPECT_EQ(out, "10 10\n");
}

// §14.13 with §23.6: a clockvar read through a path is the block's latest
// sample whichever way the path is written -- headed by a top module's name,
// `t.cb.v` of the top's own block and `t.u.cb.v` of its instance's, or
// downward from the reader, `u.cb.v` -- and from a module or a program. Read
// through a path from the root, the block was not found and the read gave the
// value before the first clocking event.
TEST(ClockingSampleSim, ClockvarReadThroughAnyPathIsTheLatestSample) {
  SimFixture f;
  std::string out = RunCaptureAllTops(
      "module c;\n"
      "  logic clk = 0, v = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input v;\n"
      "  endclocking\n"
      "  initial begin #10 clk = 1; #5 v = 1; #5 clk = 0; #10 clk = 1; end\n"
      "endmodule\n"
      "module t;\n"
      "  logic clk = 0, v = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input v;\n"
      "  endclocking\n"
      "  initial begin #10 clk = 1; #5 v = 1; #5 clk = 0; #10 clk = 1; end\n"
      "  c u();\n"
      "  initial #31 $display(\"%b%b%b\", t.cb.v, t.u.cb.v, u.cb.v);\n"
      "endmodule\n"
      "program p;\n"
      "  initial #32 $display(\"%b%b\", t.cb.v, t.u.cb.v);\n"
      "endprogram\n",
      f);
  EXPECT_EQ(out, "111\n11\n");
}

// §14.13 with §14.15 and §23.6: an event control and a wait on a clockvar
// named through a path from the root are told of the block's samples, and a
// wait on the block's event wakes at the event, all at 20 when the program's
// write of the clock makes it.
TEST(ClockingSampleSim, WaitsOnAClockvarPathFromTheRootWakeAtTheSample) {
  SimFixture f;
  std::string out = RunCaptureAllTops(
      "module m;\n"
      "  logic clk = 0, v = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input v;\n"
      "  endclocking\n"
      "endmodule\n"
      "program p;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin @(m.cb.v); $display(\"event control %0t\", $time); end\n"
      "      begin wait (m.cb.v == 1); $display(\"wait %0t\", $time); end\n"
      "    join_none\n"
      "    #15 m.v = 1;\n"
      "    #5 m.clk = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "endprogram\n",
      f);
  EXPECT_EQ(out, "event control 20\nwait 20\n$finish at time 25\n");
}

// §14.13: the same two answers for a block declared in an interface instance
// and for one declared in a program, whose inputs name a module's signals.
// Each #0 input keeps its sample through the program's writes, read by the
// #0 control as 0, and is sampled again on the new clocking event the
// program's writes make, reading 1 beside the 1step input's 0.
TEST(ClockingSampleSim, ZeroSkewInputRuleHoldsInAnInterfaceAndAProgram) {
  SimFixture f;
  std::string out = RunCaptureAllTops(
      "interface bus;\n"
      "  logic clk = 0, v = 0, u = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #0 v;\n"
      "    input #1step u;\n"
      "  endclocking\n"
      "  initial #10 clk = 1;\n"
      "endinterface\n"
      "module t;\n"
      "  bus b();\n"
      "  logic clk = 0, v = 0, u = 0;\n"
      "  initial #20 clk = 1;\n"
      "endmodule\n"
      "program p;\n"
      "  clocking pb @(posedge t.clk);\n"
      "    input #0 v = t.v;\n"
      "    input #1step u = t.u;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    @(t.b.cb);\n"
      "    t.b.v = 1; t.b.u = 1;\n"
      "    #0 $display(\"%b%b\", t.b.cb.v, t.b.cb.u);\n"
      "    fork\n"
      "      begin @(t.b.cb); $display(\"%b%b\", t.b.cb.v, t.b.cb.u); end\n"
      "      begin t.b.clk = 0; #0 t.b.clk = 1; end\n"
      "    join\n"
      "    @(pb);\n"
      "    t.v = 1; t.u = 1;\n"
      "    #0 $display(\"%b%b\", pb.v, pb.u);\n"
      "    fork\n"
      "      begin @(pb); $display(\"%b%b %0t\", pb.v, pb.u, $time); end\n"
      "      begin t.clk = 0; #0 t.clk = 1; end\n"
      "    join\n"
      "  end\n"
      "endprogram\n",
      f);
  EXPECT_EQ(out, "00\n10\n00\n10 20\n");
}

}  // namespace
