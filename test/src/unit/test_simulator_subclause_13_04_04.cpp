#include <gtest/gtest.h>

#include "fixture_simulator.h"
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

TEST(FunctionBackgroundProcessSim, TheCallerGoesOnAtOnceWhileTheForkWaits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  int x, y, t_after, x_after, y_after;\n"
                       "  task t(); #5 y = 7; endtask\n"
                       "  function void spawn_delayed();\n"
                       "    fork\n"
                       "      #10 x = 42;\n"
                       "    join_none\n"
                       "  endfunction\n"
                       "  function void spawn_task();\n"
                       "    fork\n"
                       "      t();\n"
                       "    join_none\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    x = 3;\n"
                       "    y = 4;\n"
                       "    spawn_delayed();\n"
                       "    spawn_task();\n"
                       "    t_after = $time;\n"
                       "    x_after = x;\n"
                       "    y_after = y;\n"
                       "    $display(\"%0d %0d %0d\", t_after, x_after, "
                       "y_after);\n"
                       "    #6 $display(\"%0t %0d %0d\", $time, x, y);\n"
                       "    #5 $display(\"%0t %0d %0d\", $time, x, y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 3 4\n6 3 7\n11 42 7\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionBackgroundProcessSim, TheClauseExampleWatchersRunInTheBackground) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class IntClass;\n"
                 "  int a;\n"
                 "endclass\n"
                 "module m;\n"
                 "  IntClass address = new(), stack = new();\n"
                 "  function automatic bit watch_for_zero(IntClass p);\n"
                 "    fork\n"
                 "      forever @p.a begin\n"
                 "        if (p.a == 0) $display(\"Unexpected zero\");\n"
                 "      end\n"
                 "    join_none\n"
                 "    return (p.a == 0);\n"
                 "  endfunction\n"
                 "  function bit start_check();\n"
                 "    return (watch_for_zero(address) | "
                 "watch_for_zero(stack));\n"
                 "  endfunction\n"
                 "  initial begin\n"
                 "    stack.a = 5;\n"
                 "    address.a = 6;\n"
                 "    if (start_check()) $display(\"OK\");\n"
                 "    else $display(\"not zero\");\n"
                 "    fork\n"
                 "      if (start_check()) $display(\"OK too\");\n"
                 "      else $display(\"still not zero\");\n"
                 "    join_none\n"
                 "    #1 stack.a = 9;\n"
                 "    #1 stack.a = 0;\n"
                 "    #1 $display(\"%0t done\", $time);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "not zero\nstill not zero\nUnexpected zero\nUnexpected zero\n3 done\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
