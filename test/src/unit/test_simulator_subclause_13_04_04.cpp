#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(FunctionBackgroundProcessSim, ForkJoinNoneSpawnsProcess) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  logic [7:0] x;\n"
                      "  function void set_x();\n"
                      "    fork\n"
                      "      x = 42;\n"
                      "    join_none\n"
                      "  endfunction\n"
                      "  initial set_x();\n"
                      "endmodule\n",
                      "x"),
            42u);
}

TEST(FunctionBackgroundProcessSim, ForkJoinNoneSpawnsDelayedBackgroundProcess) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  logic [7:0] x;\n"
                      "  function void spawn_delayed();\n"
                      "    fork\n"
                      "      #10 x = 42;\n"
                      "    join_none\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    x = 7;\n"
                      "    spawn_delayed();\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            42u);
}

TEST(FunctionBackgroundProcessSim, NonblockingAssignFromFunction) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  logic [7:0] x;\n"
                      "  function void set_x();\n"
                      "    x <= 99;\n"
                      "  endfunction\n"
                      "  initial set_x();\n"
                      "endmodule\n",
                      "x"),
            99u);
}

TEST(FunctionBackgroundProcessSim, EventTriggerFromFunctionWakesTheWaiter) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  event e;\n"
                      "  logic [7:0] x;\n"
                      "  function void fire();\n"
                      "    -> e;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    x = 1;\n"
                      "    @e;\n"
                      "    x = 5;\n"
                      "  end\n"
                      "  initial #1 fire();\n"
                      "endmodule\n",
                      "x"),
            5u);
}

TEST(FunctionBackgroundProcessSim, NbEventTriggerFromFunctionWakesTheWaiter) {
  EXPECT_EQ(RunAndGet("module m;\n"
                      "  event e;\n"
                      "  logic [7:0] x;\n"
                      "  function void fire();\n"
                      "    ->> e;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    x = 1;\n"
                      "    @e;\n"
                      "    x = 6;\n"
                      "  end\n"
                      "  initial #1 fire();\n"
                      "endmodule\n",
                      "x"),
            6u);
}

}  // namespace
