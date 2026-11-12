#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, DoWhileAtLeastOnce) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    do x = x + 8'd1; while (0);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LoopStatementSim, DoWhileIterates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    do x = x + 8'd1; while (x < 8'd5);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopStatementSim, DoWhileBreakExitsBeforeConditionTest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    do begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) break;\n"
      "    end while (x < 8'd10);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, DoWhileConditionTestedAfterContinue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, sum;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    sum = 8'd0;\n"
      "    do begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd2) continue;\n"
      "      sum = sum + x;\n"
      "    end while (x < 8'd4);\n"
      "  end\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(LoopStatementSim, DoWhileXConditionOneIteration) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic cond;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    cond = 1'bx;\n"
      "    do x = x + 8'd1; while (cond);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LoopStatementSim, DoWhileInFunctionRunsBodyBeforeTest) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [31:0] result;\n"
                      "  function automatic int count_up(input int n);\n"
                      "    count_up = 0;\n"
                      "    do count_up = count_up + 1; while (count_up < n);\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    result = count_up(0);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(LoopStatementSim, DoWhileMultiBitConditionIsTruthy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] count;\n"
      "  logic [7:0] iters;\n"
      "  initial begin\n"
      "    count = 8'd5;\n"
      "    iters = 8'd0;\n"
      "    do begin\n"
      "      count = count - 8'd1;\n"
      "      iters = iters + 8'd1;\n"
      "    end while (count);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* count = f.ctx.FindVariable("count");
  auto* iters = f.ctx.FindVariable("iters");
  ASSERT_NE(count, nullptr);
  ASSERT_NE(iters, nullptr);
  EXPECT_EQ(count->value.ToUint64(), 0u);
  EXPECT_EQ(iters->value.ToUint64(), 5u);
}

TEST(DoWhileLoopExampleSim, TheMapExampleVisitsEveryKeyOnce) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int map [string];\n"
                       "  task automatic show;\n"
                       "    string s;\n"
                       "    if ( map.first( s ) )\n"
                       "       do\n"
                       "          $display( \"%s : %d\\n\", s, map[ s ] );\n"
                       "       while ( map.next( s ) );\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    show;\n"
                       "    map[\"b\"] = 2;\n"
                       "    show;\n"
                       "    map[\"c\"] = 3;\n"
                       "    map[\"a\"] = 1;\n"
                       "    show;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "b :           2\n\na :           1\n\nb :           2\n\nc :      "
            "     3\n\n");
}

}  // namespace
