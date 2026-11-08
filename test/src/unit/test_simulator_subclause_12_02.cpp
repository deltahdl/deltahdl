#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ProceduralStatementContainmentSim, InitialRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(ProceduralStatementContainmentSim, AlwaysRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin x = 0; #10 $finish; end\n"
      "  always #3 x = x + 1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 3u);
}

TEST(ProceduralStatementContainmentSim, AlwaysCombRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x, y;\n"
      "  initial y = 7;\n"
      "  always_comb x = y + 1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 8u);
}

TEST(ProceduralStatementContainmentSim, AlwaysLatchRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic en;\n"
      "  logic [31:0] x, y;\n"
      "  initial begin en = 1; y = 5; end\n"
      "  always_latch if (en) x = y;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 5u);
}

TEST(ProceduralStatementContainmentSim, AlwaysFFRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic clk;\n"
      "  logic [31:0] x, y;\n"
      "  initial begin clk = 0; y = 9; #1 clk = 1; #1 $finish; end\n"
      "  always_ff @(posedge clk) x <= y;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 9u);
}

TEST(ProceduralStatementContainmentSim, FinalRunsItsStatement) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial begin x = 1; #5 $finish; end\n"
      "  final x = 99;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 99u);
}

TEST(ProceduralStatementContainmentSim, TaskRunsItsStatementWhenCalled) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  task set_x;\n"
      "    x = 21;\n"
      "  endtask\n"
      "  initial begin x = 0; set_x(); end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 21u);
}

TEST(ProceduralStatementContainmentSim, FunctionRunsItsStatementsWhenCalled) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  function int add_one(input int v);\n"
      "    int t;\n"
      "    t = v + 1;\n"
      "    return t;\n"
      "  endfunction\n"
      "  initial x = add_one(16);\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 17u);
}

}  // namespace
