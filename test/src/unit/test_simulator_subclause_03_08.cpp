#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(SubroutineFormsSim, TaskIsCalledAsAStatementWithEveryArgumentDirection) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  int o, io, rf;\n"
                 "  task automatic exchange(input int i, output int out,\n"
                 "                          inout int both, ref int r);\n"
                 "    out = i + 1;\n"
                 "    both = both * 2;\n"
                 "    r = r + 10;\n"
                 "  endtask\n"
                 "  initial begin\n"
                 "    io = 3;\n"
                 "    rf = 5;\n"
                 "    exchange(7, o, io, rf);\n"
                 "    $display(\"o=%0d io=%0d rf=%0d\", o, io, rf);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "o=8 io=6 rf=15\n");
}

TEST(SubroutineFormsSim, TaskBlocksSimulationTimeAndExitsLater) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  task pause(input int cycles);\n"
                       "    #(cycles);\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    $display(\"enter=%0t\", $time);\n"
                       "    pause(4);\n"
                       "    $display(\"exit=%0t\", $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "enter=0\nexit=4\n");
}

TEST(SubroutineFormsSim, NonvoidFunctionCallIsAnOperand) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  function int square(int x);\n"
                       "    return x * x;\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d\", square(3) + square(4));\n"
                       "endmodule\n",
                       f),
            "25\n");
}

TEST(SubroutineFormsSim, VoidFunctionIsCalledAsAStatement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int total = 0;\n"
                       "  function void add(int x);\n"
                       "    total = total + x;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    add(5);\n"
                       "    add(6);\n"
                       "    $display(\"total=%0d\", total);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "total=11\n");
}

TEST(SubroutineFormsSim, FunctionTakesEveryArgumentDirection) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  int o, io, rf, ret;\n"
                       "  function automatic int exchange(input int i,\n"
                       "      output int out, inout int both, ref int r);\n"
                       "    out = i - 1;\n"
                       "    both = both + 100;\n"
                       "    r = r * 3;\n"
                       "    return i * 2;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    io = 1;\n"
                       "    rf = 4;\n"
                       "    ret = exchange(9, o, io, rf);\n"
                       "    $display(\"ret=%0d o=%0d io=%0d rf=%0d\", ret, o, "
                       "io, rf);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ret=18 o=8 io=101 rf=12\n");
}

TEST(SubroutineFormsSim, FunctionReturnsAtOnceButForksAProcessThatBlocks) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  logic done = 0;\n"
                       "  function void launch();\n"
                       "    fork\n"
                       "      #5 done = 1;\n"
                       "    join_none\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    launch();\n"
                       "    $display(\"t=%0t done=%0d\", $time, done);\n"
                       "    #6 $display(\"t=%0t done=%0d\", $time, done);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=0 done=0\nt=6 done=1\n");
}

}  // namespace
