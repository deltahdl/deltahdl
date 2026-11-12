#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(SubroutineOverviewSim,
     TheSwitchBytesTaskPlacesTheReversedBytesInItsOutput) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic [15:0] old_word, new_word;\n"
                       "  task switch_bytes(input logic [15:0] w,\n"
                       "                    output logic [15:0] s);\n"
                       "    s = {w[7:0], w[15:8]};\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    old_word = 16'h12ab;\n"
                       "    switch_bytes (old_word, new_word);\n"
                       "    $display(\"%h %h\", old_word, new_word);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "12ab ab12\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SubroutineOverviewSim, TheSwitchBytesFunctionReturnsTheReversedBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic [15:0] old_word, new_word;\n"
                       "  function logic [15:0] switch_bytes(\n"
                       "      input logic [15:0] w);\n"
                       "    return {w[7:0], w[15:8]};\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    old_word = 16'h12ab;\n"
                       "    new_word = switch_bytes (old_word);\n"
                       "    $display(\"%h %h\", old_word, new_word);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "12ab ab12\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SubroutineOverviewSim, AFunctionTakesNoTimeWhileATaskMayTakeTime) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  int a, b, v, w;\n"
                       "  function int inc(int x);\n"
                       "    return x + 1;\n"
                       "  endfunction\n"
                       "  task dbl(input int x, output int y);\n"
                       "    #5 y = x * 2;\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    #1;\n"
                       "    v = inc(4);\n"
                       "    a = $time;\n"
                       "    dbl(v, w);\n"
                       "    b = $time;\n"
                       "    $display(\"%0d %0d %0d %0d\", a, v, b, w);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 5 6 10\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(SubroutineOverviewSim, ATaskEnablesATaskAndCallsAFunction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  int r;\n"
                       "  task inner(output int y);\n"
                       "    #2 y = 7;\n"
                       "  endtask\n"
                       "  function int dbl(int x);\n"
                       "    return 2 * x;\n"
                       "  endfunction\n"
                       "  task outer(output int z);\n"
                       "    int t;\n"
                       "    inner(t);\n"
                       "    z = dbl(t) + 1;\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    outer(r);\n"
                       "    $display(\"%0d %0d\", r, $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "15 2\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
