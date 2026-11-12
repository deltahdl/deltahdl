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
  auto [clk, data] = CreateClockAndSignal(f, 0, "data_in", 8, 0xAB);

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
  auto [clk, data] = CreateClockAndSignal(f, 0, "data", 8, 0x11);

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
  auto [clk, data] = CreateClockAndSignal(f, 0, "data", 8, 0x10);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput, true});

  SchedulePosedge(f, clk, 10);

  ScheduleValueChange(f, data, 10, 0x20);

  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x20u);
}

TEST(InputSamplingSim, NonZeroSkewInputDoesNotSampleSameStepActiveUpdate) {
  ClockingSimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, 0, "data", 8, 0x10);

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
  sig.is_explicit_zero_skew = false;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);

  ScheduleValueChange(f, data, 10, 0x20);

  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x10u);
}

TEST(InputSamplingSim, ClockvarReadStaysFrozenBetweenEdges) {
  SimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, 0, "data", 8, 0xA5);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);

  ScheduleValueChange(f, data, 15, 0x3C);

  f.scheduler.Run();

  EXPECT_EQ(data->value.ToUint64(), 0x3Cu);

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
  auto [clk, data] = CreateClockAndSignal(f, 0, "data", 8, 0x55);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInout});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x55u);
}

TEST(InputSamplingSim, SampledBeforeBlockEventFires) {
  ClockingSimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, 0, "data", 8, 0x42);

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

TEST(InputSamplingSim, InoutClockvarReadYieldsSampledValue) {
  SimFixture f;
  auto [clk, data] = CreateClockAndSignal(f, 0, "data", 8, 0x5A);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInout});
  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(ReadClockvar(f, "cb", "data"), 0x5Au);
}

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

TEST(ClockingSampleSim, AProgramReadsTheSampleFromBeforeTheDesignsEdgeUpdate) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program tb(input logic clk, input logic [7:0] d);\n"
                       "  clocking cb @(posedge clk);\n"
                       "    input d;\n"
                       "  endclocking\n"
                       "  initial begin\n"
                       "    @(cb);\n"
                       "    $display(\"%0d %0d\", cb.d, d);\n"
                       "    @(cb);\n"
                       "    $display(\"%0d %0d\", cb.d, d);\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  logic [7:0] d = 5;\n"
                       "  always #5 clk = ~clk;\n"
                       "  always @(posedge clk) d <= d + 1;\n"
                       "  tb t(clk, d);\n"
                       "endmodule\n",
                       f),
            "5 6\n6 7\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClockingSampleSim, ASkewedInputTakesThePostponedValueThatManyUnitsBefore) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  logic clk = 0;\n"
                       "  logic [7:0] v = 0;\n"
                       "  clocking cb @(posedge clk);\n"
                       "    input #3 v;\n"
                       "  endclocking\n"
                       "  initial begin\n"
                       "    #6 v = 1;\n"
                       "    #1 v = 2;\n"
                       "    #1 v = 3;\n"
                       "    #1 v = 4;\n"
                       "    #1 clk = 1;\n"
                       "    #1 $display(\"%0d\", cb.v);\n"
                       "    v = 5; #3 v = 6; #2 v = 7;\n"
                       "    clk = 0; #1 clk = 1;\n"
                       "    #1 $display(\"%0d\", cb.v);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2\n6\n$finish at time 18\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
