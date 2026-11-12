#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(InoutDriveSim, ADriveLeavesTheInoutSampleUntilTheNextEvent) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  logic a = 0, b = 1, c = 1, s = 0;\n"
                       "  clocking cb @(posedge clk);\n"
                       "    inout a;\n"
                       "    output b;\n"
                       "    input #2 output s;\n"
                       "  endclocking\n"
                       "  initial begin\n"
                       "    @(cb);\n"
                       "    cb.a <= c;\n"
                       "    cb.b <= cb.a;\n"
                       "    #1 $display(\"cb.a=%b a=%b b=%b\", cb.a, a, b);\n"
                       "    #6 s = 1;\n"
                       "    #2 s = 0;\n"
                       "    #2 $display(\"cb.a=%b cb.s=%b\", cb.a, cb.s);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "cb.a=0 a=1 b=0\ncb.a=1 cb.s=1\n$finish at time 16\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(InoutDriveSim, AProgramReadsTheOldSampleAfterTheDriveUpdates) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program tb(input logic clk);\n"
                 "  clocking cb @(posedge clk);\n"
                 "    inout a = m.a;\n"
                 "    output b = m.b;\n"
                 "  endclocking\n"
                 "  initial begin\n"
                 "    @(cb);\n"
                 "    cb.a <= 1'b1;\n"
                 "    cb.b <= cb.a;\n"
                 "    #1 $display(\"cb.a=%b a=%b b=%b\", cb.a, m.a, m.b);\n"
                 "    @(cb);\n"
                 "    #1 $display(\"cb.a=%b\", cb.a);\n"
                 "  end\n"
                 "endprogram\n"
                 "module m;\n"
                 "  logic clk = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "  logic a = 0, b = 1;\n"
                 "  tb t(clk);\n"
                 "endmodule\n",
                 f),
      "cb.a=0 a=1 b=0\ncb.a=1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(InoutDriveSim, DISABLED_AnInoutNetSamplesTheResolvedValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module drv(output wire o);\n"
                       "  assign o = 1'b0;\n"
                       "endmodule\n"
                       "module m;\n"
                       "  logic clk = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  wire w;\n"
                       "  drv d(w);\n"
                       "  clocking cb @(posedge clk);\n"
                       "    inout w;\n"
                       "  endclocking\n"
                       "  initial begin\n"
                       "    @(cb);\n"
                       "    $display(\"cb.w=%b w=%b\", cb.w, w);\n"
                       "    cb.w <= 1'b1;\n"
                       "    #1 $display(\"cb.w=%b w=%b\", cb.w, w);\n"
                       "    @(cb);\n"
                       "    #1 $display(\"cb.w=%b w=%b\", cb.w, w);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "cb.w=0 w=0\ncb.w=0 w=x\ncb.w=x w=x\n$finish at time 16\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
