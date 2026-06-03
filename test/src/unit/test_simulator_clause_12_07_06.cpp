#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, ForeverBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopStatementSim, ForeverContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(LoopStatementSim, ForeverImmediateBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.7.6: the forever-loop repeatedly executes its statement. The three tests
// above exercise the statement scheduler (ExecForever); this one observes the
// same repeated execution on the function-body path, where the loop is
// interpreted by ExecFuncForever. accumulate(5) runs the body once per pass,
// summing 1+2+3+4+5 across five iterations before the return ends the loop.
TEST(LoopStatementSim, ForeverInFunctionRunsBodyRepeatedly) {
  EXPECT_EQ(RunAndGet(
                "module t;\n"
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

// §12.7.6: a forever-loop repeatedly executes its statement. The other tests
// run the loop to completion within a single time step (it ends via break or
// return). This one exercises the canonical use shown in the subclause — a body
// guarded by a timing control — so ExecForever suspends on each #10 delay and
// is resumed by the scheduler on the next time step, executing the body once
// per step. A parallel process ends the run with $finish after the fourth tick
// but before the fifth, so the counter observes exactly four iterations.
TEST(LoopStatementSim, ForeverWithDelayIteratesAcrossSimTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] ticks;\n"
      "  initial begin\n"
      "    ticks = 8'd0;\n"
      "    forever #10 ticks = ticks + 8'd1;\n"
      "  end\n"
      "  initial #45 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("ticks");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

}
