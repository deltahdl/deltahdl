#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(FunctionBackgroundProcessSim, ForkJoinNoneSpawnsProcess) {
  EXPECT_EQ(RunAndGet(
                "module m;\n"
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

TEST(FunctionBackgroundProcessSim, NonblockingAssignFromFunction) {
  EXPECT_EQ(RunAndGet(
                "module m;\n"
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
