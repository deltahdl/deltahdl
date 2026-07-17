#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, RepeatCount) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    repeat (5) x = x + 8'd1;\n"
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

TEST(LoopStatementSim, RepeatZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    repeat (0) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "    repeat (3) begin\n"
      "      a = a + 8'd1;\n"
      "      b = b + 8'd2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 3u);
  EXPECT_EQ(vb->value.ToUint64(), 6u);
}

TEST(LoopStatementSim, RepeatVariableCount) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] n, x;\n"
      "  initial begin\n"
      "    n = 8'd4;\n"
      "    x = 8'd0;\n"
      "    repeat (n) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, RepeatExpressionCount) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    n = 8'd3;\n"
      "    total = 8'd0;\n"
      "    repeat (n + 8'd2)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopStatementSim, RepeatXCountZeroIterations) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    n = 8'bx;\n"
      "    repeat (n) x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatNegativeCountZeroIterations) {
  // §12.7.2: a negative count (signed expression) is treated as zero, so the
  // body never runs. Without negative handling, the bit pattern of -1 would be
  // read as a huge unsigned iteration count.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int n;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    n = -1;\n"
      "    repeat (n) x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatCountEvaluatedOnceBeforeLoop) {
  // §12.7.2: the count expression is evaluated once before the loop starts;
  // mutating the controlling variable inside the body has no effect on the
  // number of iterations.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] n, x;\n"
      "  initial begin\n"
      "    n = 8'd3;\n"
      "    x = 8'd0;\n"
      "    repeat (n) begin\n"
      "      x = x + 8'd1;\n"
      "      n = 8'd10;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, RepeatZCountZeroIterations) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    n = 8'bz;\n"
      "    repeat (n) x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatParameterCount) {
  // §12.7.2: the count expression may be sourced from a parameter (§11.2.1) --
  // the very form the LRM's multiplier example uses, "repeat (size)". The
  // parameter is resolved during elaboration and read once before the loop.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter size = 6;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    repeat (size) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(LoopStatementSim, RepeatLocalparamCount) {
  // §12.7.2: a localparam (another §11.2.1 constant form) as the repeat count
  // drives the same evaluate-once-then-iterate behaviour as a parameter.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int cnt = 7;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    repeat (cnt) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(LoopStatementSim, RepeatCompoundCountCachedWhenOperandMutated) {
  // §12.7.2: the count expression is evaluated exactly once before the loop
  // starts, so changing *any part* of a compound count expression inside the
  // body has no effect on the iteration count. Here the count is a+b; mutating
  // operand a inside the loop must not extend the run.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, x;\n"
      "  initial begin\n"
      "    a = 8'd2;\n"
      "    b = 8'd1;\n"
      "    x = 8'd0;\n"
      "    repeat (a + b) begin\n"
      "      x = x + 8'd1;\n"
      "      a = 8'd50;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, RepeatPartiallyUnknownCountZeroIterations) {
  // §12.7.2: a single unknown bit makes the whole count unknown, so it is
  // treated as zero and the body never runs. Were the known bits used instead,
  // this pattern would suggest several iterations.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    n = 8'b0000010x;\n"
      "    repeat (n) x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatGenvarCount) {
  // §12.7.2: the count expression may be a genvar (§11.2.1), which is admitted
  // only inside a generate scope and substituted as a per-instance constant.
  // Each unrolled instance runs its body the genvar's value of times, so the
  // element written by instance i ends at i.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] out [0:3];\n"
      "  generate\n"
      "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
      "      initial begin\n"
      "        out[i] = 8'd0;\n"
      "        repeat (i) out[i] = out[i] + 8'd1;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* e0 = f.ctx.FindVariable("out[0]");
  auto* e1 = f.ctx.FindVariable("out[1]");
  auto* e2 = f.ctx.FindVariable("out[2]");
  auto* e3 = f.ctx.FindVariable("out[3]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  ASSERT_NE(e3, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 0u);
  EXPECT_EQ(e1->value.ToUint64(), 1u);
  EXPECT_EQ(e2->value.ToUint64(), 2u);
  EXPECT_EQ(e3->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, RepeatConstantFunctionCallCount) {
  // §12.7.2: the count expression may be a function call (the last §11.2.1
  // constant form), which takes the call-evaluation path rather than a plain
  // variable read. The returned value is read once before the loop and drives
  // the iteration count.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function automatic logic [7:0] three();\n"
      "    three = 8'd3;\n"
      "  endfunction\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    repeat (three()) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

}  // namespace
