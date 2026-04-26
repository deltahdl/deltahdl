#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

// §4.9.1 atom: a continuous assignment statement corresponds to a process.
// Observed by lowering `assign b = a;` and checking that `b` carries the
// value driven through the assignment after `Scheduler::Run` — only possible
// when `Lowerer::LowerContAssign` produced a schedulable process backing the
// statement.
TEST(ContinuousAssignSchedulingSim, ContinuousAssignmentCorrespondsToProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  assign b = a;\n"
      "  initial a = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 55u);
}

// §4.9.1 atom: the continuous-assignment process is sensitive to the source
// elements in the expression. Observed by changing the source after time 0
// and checking the target tracks the new source value — a non-sensitive
// process would leave the target stuck at the time-0 sample.
TEST(ContinuousAssignSchedulingSim, SensitiveToSourceElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, dst;\n"
      "  assign dst = src;\n"
      "  initial begin\n"
      "    src = 8'd1;\n"
      "    #10 src = 8'd200;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 200u);
}

// §4.9.1 atom (atom 2 edge case — plural "source elements"): the CA process
// is sensitive to every source element in the expression, not just the first.
// Observed by an `a + b` CA where only `a` is changed mid-simulation; the
// target must combine the new `a` with the current `b` value, which proves
// both inputs were registered as sources and the unchanged input still
// contributes its current value to the result.
TEST(ContinuousAssignSchedulingSim, SensitiveToMultipleSourceElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, sum;\n"
      "  assign sum = a + b;\n"
      "  initial begin\n"
      "    a = 8'd3;\n"
      "    b = 8'd4;\n"
      "    #10 a = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sum")->value.ToUint64(), 24u);
}

// §4.9.1 atom: when the value of the expression changes, the CA causes an
// active update event added to the event region, using current values to
// determine the target. Observed via two chained CAs: when `src` changes,
// `mid = src + 1` updates in the active region, then `observed = mid * 2`
// re-evaluates against the just-updated `mid` within the same timestep.
TEST(ContinuousAssignSchedulingSim, ActiveUpdateEventUsesCurrentValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, mid, observed;\n"
      "  assign mid = src + 8'd1;\n"
      "  assign observed = mid * 8'd2;\n"
      "  initial src = 8'd9;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("mid")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("observed")->value.ToUint64(), 20u);
}

// §4.9.1 atom: a continuous assignment process is also evaluated at time
// zero in order to propagate constant values. Observed by a CA whose RHS is
// a literal with no procedural drives — only a time-zero evaluation makes
// the target hold the literal value at end-of-run with `CurrentTime` still
// at tick 0.
TEST(ContinuousAssignSchedulingSim, EvaluatedAtTimeZeroForConstantPropagation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] k;\n"
      "  assign k = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("k")->value.ToUint64(), 42u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

// §4.9.1 atom (atom 4 edge case — the time-zero pass evaluates the RHS
// expression, not just a literal copy): a CA whose RHS is a constant
// arithmetic expression has its target hold the folded result at time zero.
// A literal-only fast-path would not satisfy this; only a real expression
// evaluation inside the CA process at t=0 produces the computed value.
TEST(ContinuousAssignSchedulingSim,
     ConstantExpressionEvaluatedAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] computed;\n"
      "  assign computed = 8'd5 + 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("computed")->value.ToUint64(), 8u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}
