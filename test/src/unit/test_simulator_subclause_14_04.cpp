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

}  // namespace
