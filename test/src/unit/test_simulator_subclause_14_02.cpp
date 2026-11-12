#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ClockingBlockOverviewSim, EachBlockOfAModuleFollowsItsOwnClock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  bit ca = 0, cb = 0;\n"
                       "  int a = 1, b = 2, c = 3, d = 4;\n"
                       "  int tn, ta, va, tb, vb, vc, vd;\n"
                       "  always #5 ca = ~ca;\n"
                       "  always #7 cb = ~cb;\n"
                       "  clocking none @(posedge ca);\n"
                       "  endclocking\n"
                       "  clocking ka @(posedge ca);\n"
                       "    input a;\n"
                       "  endclocking : ka\n"
                       "  clocking kb @(posedge cb);\n"
                       "    input b, c;\n"
                       "    input d;\n"
                       "  endclocking\n"
                       "  initial begin @(none); @(none); tn = $time; end\n"
                       "  initial begin\n"
                       "    #6 a = 5;\n"
                       "    @(ka); ta = $time; va = ka.a;\n"
                       "  end\n"
                       "  initial begin\n"
                       "    #8 b = 6;\n"
                       "    @(kb); tb = $time; vb = kb.b; vc = kb.c; vd = "
                       "kb.d;\n"
                       "  end\n"
                       "  initial #30 begin\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", tn, ta, "
                       "va, tb, vb, vc, vd);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "15 15 5 21 6 3 4\n$finish at time 30\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClockingBlockOverviewSim, AnInterfaceAndAProgramEachHoldTheirOwnBlocks) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface bus(input logic clk1, input logic clk2);\n"
                       "  int x, y;\n"
                       "  clocking c1 @(posedge clk1); input x; endclocking\n"
                       "  clocking c2 @(posedge clk2); output y; endclocking\n"
                       "endinterface\n"
                       "program p(bus i);\n"
                       "  clocking pc @(posedge i.clk2);\n"
                       "    input x = i.x;\n"
                       "  endclocking\n"
                       "  initial begin\n"
                       "    i.x = 9;\n"
                       "    @(i.c1) $display(\"c1 %0t %0d\", $time, i.c1.x);\n"
                       "    @(pc) $display(\"pc %0t %0d\", $time, pc.x);\n"
                       "    i.c2.y <= 3;\n"
                       "    @(i.c2); @(i.c2) $display(\"y %0d\", i.y);\n"
                       "  end\n"
                       "endprogram\n"
                       "module top;\n"
                       "  bit k1 = 0, k2 = 0;\n"
                       "  always #5 k1 = ~k1;\n"
                       "  always #7 k2 = ~k2;\n"
                       "  bus i(k1, k2);\n"
                       "  p pp(i);\n"
                       "endmodule\n",
                       f),
            "c1 5 9\npc 7 9\ny 3\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
