#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

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
