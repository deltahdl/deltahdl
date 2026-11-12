#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ClockingHierExprSim, HierarchicalSignalSampled) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xCC);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data_in", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  auto sampled = cmgr.GetSampledValue("cb", "data_in");
  EXPECT_EQ(sampled, 0xCCu);
}

TEST(ClockingHierExprSim, OutputHierSignalDriven) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  TestOutputSkewDrive(f, cmgr, 0xBEu);
}

TEST(ClockingHierExprSim, InoutHierSignalBidirectional) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* bidir = f.ctx.CreateVariable("bidir", 8);
  bidir->value = MakeLogic4VecVal(f.arena, 8, 0xEE);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, SimTime{2}, "bidir", ClockingDir::kInout});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "bidir"), 0xEEu);

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "bidir", 0x11, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{20}, Region::kActive, ev);
  f.scheduler.Run();
  EXPECT_EQ(bidir->value.ToUint64(), 0x11u);
}

TEST(ClockingHierExprSim, ClockvarBoundToAnotherNameSamplesIt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  logic [3:0] state = 2;\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic clk = 0;\n"
                       "  sub u();\n"
                       "  clocking cb @(posedge clk);\n"
                       "    input st = u.state;\n"
                       "  endclocking\n"
                       "  always #5 clk = ~clk;\n"
                       "  initial begin\n"
                       "    #7 u.state = 6;\n"
                       "  end\n"
                       "  initial begin\n"
                       "    @(cb); @(cb);\n"
                       "    $display(\"t=%0t st=%0d\", $time, cb.st);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=15 st=6\n$finish at time 15\n");
}

TEST(ClockingHierExprSim, ProgramClockvarSamplesACrossModuleSignal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module cpu;\n"
                       "  logic [3:0] state = 6;\n"
                       "endmodule\n"
                       "program test(input logic clk);\n"
                       "  clocking cd1 @(posedge clk);\n"
                       "    input state = top.cpu1.state;\n"
                       "  endclocking\n"
                       "  initial begin\n"
                       "    @(cd1);\n"
                       "    $display(\"t=%0t state=%0d\", $time, cd1.state);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  cpu cpu1();\n"
                       "  test main(clk);\n"
                       "endmodule\n",
                       f),
            "t=5 state=6\n$finish at time 5\n");
}

TEST(ClockingHierExprSim, OutputClockvarDrivesTheSignalItsExpressionNames) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  logic clk = 0; logic [3:0] d;\n"
          "  always #5 clk = ~clk;\n"
          "  always @(d) $display(\"mod d=%0d at %0t\", d, $time);\n"
          "  p pi();\n"
          "endmodule\n"
          "program p;\n"
          "  clocking cb @(posedge top.clk); output d = top.d; endclocking\n"
          "  initial begin @(cb); cb.d <= 4'd5; @(cb); #1; end\n"
          "endprogram\n",
          f),
      "mod d=5 at 5\n");
}

TEST(ClockingHierExprSim, ClockvarBoundToASliceOrConcatenation) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  logic clk = 0;\n"
          "  logic [3:0] opcode = 4'b1010, regA = 4'b0110, regB = 4'b0101;\n"
          "  logic [7:0] q = 8'b11110000;\n"
          "  clocking cb @(posedge clk);\n"
          "    input instr = {opcode, regA, regB[3:1]};\n"
          "    output nib = q[3:0];\n"
          "  endclocking\n"
          "  always #5 clk = ~clk;\n"
          "  initial begin\n"
          "    @(cb);\n"
          "    cb.nib <= 4'b0101;\n"
          "    #1 $display(\"%b %b\", cb.instr, q);\n"
          "    $finish;\n"
          "  end\n"
          "endmodule\n",
          f),
      "10100110010 11110101\n$finish at time 6\n");
}

TEST(ClockingHierExprSim, ADriveThroughAConcatenationSplitsAcrossItsSignals) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  logic [3:0] hi = 0;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  logic [3:0] lo = 0, c = 4'b0011;\n"
                       "  logic s = 1;\n"
                       "  sub u();\n"
                       "  always #5 clk = ~clk;\n"
                       "  clocking cb @(posedge clk);\n"
                       "    output w = {u.hi, lo[3:2]};\n"
                       "    inout  v = {c, s};\n"
                       "  endclocking\n"
                       "  initial begin\n"
                       "    @(cb);\n"
                       "    $display(\"v=%b\", cb.v);\n"
                       "    cb.w <= 6'b101011;\n"
                       "    cb.v <= 5'b11000;\n"
                       "    @(cb); #1;\n"
                       "    $display(\"hi=%b lo=%b c=%b s=%b\", u.hi, lo, c, "
                       "s);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "v=00111\nhi=1010 lo=1100 c=1100 s=0\n$finish at time 16\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
