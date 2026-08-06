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

// §13.4.4: a function executes with no delay, so the calling process returns
// immediately even when the function spawns a fork-join_none whose body is time
// controlled. The spawned thread persists as a background process and completes
// at a later simulation time (here #10), which the caller does not wait for.
// Observing the final value proves the delayed background assignment ran after
// the call — and the initial block that made it — had already returned.
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

}  // namespace
