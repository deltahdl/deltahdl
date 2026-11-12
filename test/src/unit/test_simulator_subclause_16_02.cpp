#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(AssertionKindSim,
     ConcurrentAndImmediateAssertAssumeAndCoverRunTheirActions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  bit clk = 0, a = 0;\n"
                       "  int ca = 0, cu = 0, cc = 0, ia = 0, iu = 0, ic = 0;\n"
                       "  always #5 clk = ~clk;\n"
                       "  assert property (@(posedge clk) a) else ca++;\n"
                       "  assume property (@(posedge clk) a) else cu++;\n"
                       "  cover property (@(posedge clk) !a) cc++;\n"
                       "  initial begin\n"
                       "    assert (a) else ia++;\n"
                       "    assume (a) else iu++;\n"
                       "    cover (!a) ic++;\n"
                       "    #22 $display(\"%0d %0d %0d | %0d %0d %0d\", ca, "
                       "cu, cc, ia, iu, ic);\n"
                       "    $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 2 2 | 1 1 1\n$finish at time 22\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
