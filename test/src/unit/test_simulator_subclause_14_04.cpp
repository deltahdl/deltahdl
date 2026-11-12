#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_preprocess_and_get.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ClockingSkewSim, PerSignalSkewOverride) {
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

TEST(ClockingSkewSim, InoutSignalDirection) {
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

TEST(ClockingSkewSim, InputSkewSamplesBeforeClockEdge) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{2};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "data_in";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  auto sampled = cmgr.GetSampledValue("cb", "data_in");
  EXPECT_EQ(sampled, 0xABu);
}

TEST(ClockingSkewSim, OutputSkewDelaysDriveBySkewAmount) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data_out = f.ctx.CreateVariable("data_out", 8);
  data_out->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr,
                     {"cb",
                      Edge::kPosedge,
                      {0},
                      SimTime{5},
                      "data_out",
                      ClockingDir::kOutput});

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "data_out", 0x77, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);

  uint64_t mid_value = 0xFF;
  auto* probe = f.scheduler.GetEventPool().Acquire();
  probe->callback = [&mid_value, data_out]() {
    mid_value = data_out->value.ToUint64();
  };
  f.scheduler.ScheduleEvent(SimTime{12}, Region::kActive, probe);

  f.scheduler.Run();

  EXPECT_EQ(mid_value, 0x00u);
  EXPECT_EQ(data_out->value.ToUint64(), 0x77u);
}

TEST(ClockingSkewSim, PerSignalOutputSkewOverride) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{10};

  ClockingSignal sig;
  sig.signal_name = "fast_out";
  sig.direction = ClockingDir::kOutput;
  sig.skew = SimTime{2};
  block.signals.push_back(sig);
  cmgr.Register(block);

  EXPECT_EQ(cmgr.GetOutputSkew("cb", "fast_out").ticks, 2u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "other").ticks, 10u);
}

TEST(ClockingSkewSim, ZeroOutputSkewDrivesInReNbaRegion) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data_out = f.ctx.CreateVariable("data_out", 8);
  data_out->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr,
                     {"cb",
                      Edge::kPosedge,
                      {0},
                      SimTime{0},
                      "data_out",
                      ClockingDir::kOutput});

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "data_out", 0x42, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(data_out->value.ToUint64(), 0x42u);
}

TEST(ClockingSkewSim, OneStepInputSkewSamplesPreEdgeValue) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("step_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x11);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{1};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "step_in";
  sig.direction = ClockingDir::kInput;
  sig.is_one_step_skew = true;
  block.signals.push_back(sig);
  cmgr.Register(block);

  cmgr.Attach(f.ctx, f.scheduler);

  auto* settle = f.scheduler.GetEventPool().Acquire();
  settle->callback = []() {};
  f.scheduler.ScheduleEvent(SimTime{5}, Region::kActive, settle);

  auto* change = f.scheduler.GetEventPool().Acquire();
  change->callback = [data, &f]() {
    data->value = MakeLogic4VecVal(f.arena, 8, 0x22);
    data->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, change);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "step_in"), 0x11u);
  EXPECT_EQ(data->value.ToUint64(), 0x22u);
}

TEST(ClockingSkewSim, ExplicitZeroInputSkewSampledAtClockEvent) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("z_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xCD);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "z_in";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{0};
  sig.is_explicit_zero_skew = true;
  block.signals.push_back(sig);
  cmgr.Register(block);

  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "z_in"), 0xCDu);
}

TEST(ClockingSkewSim, DefaultSkewValues) {
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

  EXPECT_EQ(cmgr.GetInputSkew("cb", "data").ticks, 0u);
  EXPECT_EQ(cmgr.GetOutputSkew("cb", "data").ticks, 0u);
}

TEST(ClockingSkewSim, NumericInputSkewSamplesThatLongBeforeTheEdge) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  parameter S = 2;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] d = 11;\n"
      "  clocking c1 @(posedge clk); input #1 d; endclocking\n"
      "  clocking c2 @(posedge clk); input #3 d; endclocking\n"
      "  clocking c3 @(posedge clk); input #1step d; endclocking\n"
      "  clocking c4 @(posedge clk); default input #2; input d; endclocking\n"
      "  clocking c5 @(posedge clk); input #S d; endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin #12 d = 12; #1 d = 13; #1 d = 14; #1 d = 15; end\n"
      "  initial begin\n"
      "    @(posedge clk); @(posedge clk); #0;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", c1.d, c2.d, c3.d, c4.d, c5.d);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "14 12 14 13 13\n$finish at time 15\n");
}

TEST(ClockingSkewSim, EdgeSkewSamplesAndDrivesAtThatEdge) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] d = 1, q = 0;\n"
      "  clocking cb @(posedge clk);\n"
      "    input negedge d;\n"
      "    output negedge q;\n"
      "  endclocking\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin #7 d = 2; #5 d = 3; end\n"
      "  initial begin\n"
      "    @(posedge clk); cb.q <= 6;\n"
      "    #4 $write(\"%0d \", q);\n"
      "    #2 $write(\"%0d \", q);\n"
      "    @(cb); $display(\"%0d\", cb.d);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 6 2\n$finish at time 15\n");
}

TEST(ClockingSkewSim,
     AUnitlessSkewTakesTheTimescaleUnitAndALiteralKeepsItsOwn) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture(
          "`timescale 10ns/1ps\n"
          "module t;\n"
          "  parameter P = 1;\n"
          "  logic clk = 0;\n"
          "  int a = 0, b = 0, c = 0, d = 0, e = 0, o1 = 0, o2 = 0;\n"
          "  real tq1 = -1, tq2 = -1;\n"
          "  always #5 clk = ~clk;\n"
          "  clocking c1 @(posedge clk);\n"
          "    input #1 a;\n"
          "    output #1 o1;\n"
          "  endclocking\n"
          "  clocking c2 @(posedge clk);\n"
          "    input #2ns b;\n"
          "    input #1ps e;\n"
          "    output #3ns o2;\n"
          "  endclocking\n"
          "  clocking c3 @(posedge clk);\n"
          "    default input #1 output #1;\n"
          "    input c;\n"
          "  endclocking\n"
          "  clocking c4 @(posedge clk);\n"
          "    input #P d;\n"
          "  endclocking\n"
          "  always @(o1) tq1 = $realtime;\n"
          "  always @(o2) tq2 = $realtime;\n"
          "  initial begin\n"
          "    #4.5 a = 1; b = 1; c = 1; d = 1;\n"
          "    #0.4 b = 2; e = 1;\n"
          "    #0.1 e = 2;\n"
          "    @(c1);\n"
          "    $display(\"a=%0d b=%0d c=%0d d=%0d e=%0d\", c1.a, c2.b, "
          "c3.c, c4.d, c2.e);\n"
          "    c1.o1 <= 7; c2.o2 <= 8;\n"
          "    #3 $display(\"o1 at %0.2f o2 at %0.2f\", tq1, tq2);\n"
          "    $finish;\n"
          "  end\n"
          "endmodule\n",
          f),
      "a=0 b=1 c=0 d=0 e=1\no1 at 6.00 o2 at 5.30\n$finish at time 80000\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClockingSkewSim, EachModuleReadsAUnitlessSkewInItsOwnTimeUnit) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module fast;\n"
                 "  timeunit 1ns; timeprecision 1ns;\n"
                 "  int v = 0, s = -1;\n"
                 "  clocking cf @(posedge top.clk);\n"
                 "    input #1 v;\n"
                 "  endclocking\n"
                 "  initial begin #96 v = 1; @(cf) s = cf.v; end\n"
                 "endmodule\n"
                 "module slow;\n"
                 "  timeunit 10ns; timeprecision 1ns;\n"
                 "  int v = 0, s = -1;\n"
                 "  clocking cs @(posedge top.clk);\n"
                 "    input #1 v;\n"
                 "  endclocking\n"
                 "  initial begin #9.6 v = 1; @(cs) s = cs.v; end\n"
                 "endmodule\n"
                 "module top;\n"
                 "  timeunit 1ns; timeprecision 1ns;\n"
                 "  logic clk = 0;\n"
                 "  initial #100 clk = 1;\n"
                 "  fast f();\n"
                 "  slow s();\n"
                 "  initial #120 $display(\"fast=%0d slow=%0d\", f.s, s.s);\n"
                 "endmodule\n",
                 f),
      "fast=1 slow=0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClockingSkewSim, AnExplicitZeroSkewSamplesInObservedAndDrivesInReNba) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  logic clk = 0;\n"
          "  int z = 0, o = 0, r1 = -1, r2 = -1;\n"
          "  always #10 clk = ~clk;\n"
          "  clocking cb @(posedge clk);\n"
          "    input #0 z;\n"
          "    output #0 o;\n"
          "  endclocking\n"
          "  always @(posedge clk) #0 z = 5;\n"
          "  always @(posedge clk) begin r1 = o; #0 r2 = o; end\n"
          "  initial begin\n"
          "    #5 cb.o <= 1;\n"
          "    @(cb);\n"
          "    #1 $display(\"z=%0d r1=%0d r2=%0d o=%0d\", cb.z, r1, r2, o);\n"
          "    $finish;\n"
          "  end\n"
          "endmodule\n",
          f),
      "z=5 r1=0 r2=0 o=1\n$finish at time 11\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClockingSkewSim, TheClauseDramExampleSamplesAndDrivesOnBothEdges) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture(
          "`timescale 1ns/1ps\n"
          "module t;\n"
          "  logic clk = 0;\n"
          "  int address = 0, data = 0, td = -1;\n"
          "  always #10 clk = ~clk;\n"
          "  clocking dram @(clk);\n"
          "    input #1ps address;\n"
          "    input #5 output #6 data;\n"
          "  endclocking\n"
          "  always @(data) td = $time;\n"
          "  initial begin\n"
          "    #9.998 address = 1;\n"
          "    #0.002 address = 2;\n"
          "    @(dram);\n"
          "    $display(\"%0t a=%0d d=%0d\", $time, dram.address, dram.data);\n"
          "    #2 data = 3;\n"
          "    #2 data = 4;\n"
          "    @(dram);\n"
          "    $display(\"%0t a=%0d d=%0d\", $time, dram.address, dram.data);\n"
          "    dram.data <= 9;\n"
          "    #15 $display(\"data=%0d at %0d\", data, td);\n"
          "    $finish;\n"
          "  end\n"
          "endmodule\n",
          f),
      "10000 a=1 d=0\n20000 a=2 d=4\ndata=9 at 26\n$finish at time 35000\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
