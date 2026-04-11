#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysProcedureSimulation, AlwaysLoopWithDelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] clk;\n"
      "  initial clk = 0;\n"
      "  always #5 clk = clk + 1;\n"
      "  initial #20 $finish;\n"
      "endmodule\n",
      "clk");
  EXPECT_EQ(val, 4u);
}

TEST(AlwaysProcedureSimulation, AlwaysCombRepeatsContinuously) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    #1 a = 2;\n"
      "    #1 a = 3;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always_comb b = a;\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(val, 3u);
}

TEST(AlwaysProcedureSimulation, AlwaysLatchRepeatsContinuously) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    a = 1;\n"
      "    #1 a = 2;\n"
      "    #1 a = 3;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always_latch if (en) b = a;\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(val, 3u);
}

TEST(AlwaysProcedureSimulation, AlwaysFFRepeatsContinuously) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] count;\n"
      "  initial begin clk = 0; count = 0; end\n"
      "  always #5 clk = ~clk;\n"
      "  always_ff @(posedge clk) count <= count + 1;\n"
      "  initial #20 $finish;\n"
      "endmodule\n",
      "count");
  EXPECT_EQ(val, 2u);
}

}  // namespace
