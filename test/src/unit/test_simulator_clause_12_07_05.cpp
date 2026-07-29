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

// A do...while-loop tests its control expression at the end of the loop
// (12.7.5); a break in the body leaves before that test is reached, even
// though the expression would still be true. The 12.8 file covers break
// itself, with a control expression that never ends the loop.
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

// A continue reaches the end of the do...while body, which is where the
// control expression is evaluated (12.7.5), so the loop still terminates on
// that expression. The 12.8 file covers continue as a jump statement.
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

// §12.7.5: the control expression is tested at the end of the loop, so the
// body runs at least once even when the condition is already false. Exercised
// here on the function-body execution path, where the loop is interpreted by
// ExecFuncDoWhile rather than the statement scheduler.
TEST(LoopStatementSim, DoWhileInFunctionRunsBodyBeforeTest) {
  // count_up(0): the body increments once before the while test reads the
  // updated value (1 < 0 is false), so the function returns 1, not 0.
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

// §12.7.5: the control expression may be any expression treatable as a Boolean,
// not just a one-bit relational result. Here the raw multi-bit counter value is
// the condition: any nonzero value is true, and the loop stops once it reaches
// zero. Counting down from 5 runs the body five times.
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

}  // namespace
