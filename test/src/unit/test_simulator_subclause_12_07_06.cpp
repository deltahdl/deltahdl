#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, ForeverBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    forever begin\n"
      "      if (x == 8'd5) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopStatementSim, ForeverContinueRepeatsBodyUntilBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, sum;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    sum = 8'd0;\n"
      "    forever begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) continue;\n"
      "      sum = sum + x;\n"
      "      if (x == 8'd5) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(LoopStatementSim, ForeverImmediateBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    forever begin\n"
      "      x = x + 8'd1;\n"
      "      break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LoopStatementSim, ForeverInFunctionRunsBodyRepeatedly) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] result;\n"
                      "  function automatic int accumulate(input int n);\n"
                      "    int i;\n"
                      "    int acc;\n"
                      "    i = 0;\n"
                      "    acc = 0;\n"
                      "    forever begin\n"
                      "      if (i == n) return acc;\n"
                      "      i = i + 1;\n"
                      "      acc = acc + i;\n"
                      "    end\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    result = accumulate(5);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(LoopStatementSim, ForeverWithDelayIteratesAcrossSimTime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] ticks;\n"
      "  initial begin\n"
      "    ticks = 8'd0;\n"
      "    forever #10 ticks = ticks + 8'd1;\n"
      "  end\n"
      "  initial #45 $finish;\n"
      "endmodule\n",
      f, "ticks");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

}  // namespace
