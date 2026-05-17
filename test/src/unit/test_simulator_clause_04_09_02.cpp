#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

TEST(ProceduralContinuousSchedulingSim, AssignCorrespondsToProcessSensitiveToSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, q;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    assign q = src;\n"
      "    #10 src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 99u);
  EXPECT_TRUE(q->is_forced);
}

TEST(ProceduralContinuousSchedulingSim, ForceCorrespondsToProcessSensitiveToSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, q;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    q = 8'd0;\n"
      "    force q = src;\n"
      "    #10 src = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 77u);
  EXPECT_TRUE(q->is_forced);
}

TEST(ProceduralContinuousSchedulingSim, ExpressionChangeUsesCurrentValuesForTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    a = 8'd3;\n"
      "    b = 8'd4;\n"
      "    force q = a + b;\n"
      "    #10 a = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 24u);
}

TEST(ProceduralContinuousSchedulingSim, DeassignDeactivatesAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, q;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    assign q = src;\n"
      "    #10 deassign q;\n"
      "    #10 src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_FALSE(q->is_forced);
  EXPECT_EQ(q->value.ToUint64(), 5u);
}

TEST(ProceduralContinuousSchedulingSim, AssignTracksCurrentValuesAcrossMultipleSources) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    assign c = a + b;\n"
      "    #10 a = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 50u);
  EXPECT_TRUE(c->is_forced);
}

TEST(ProceduralContinuousSchedulingSim, ReleaseDeactivatesForce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src, q;\n"
      "  initial begin\n"
      "    src = 8'd5;\n"
      "    q = 8'd0;\n"
      "    force q = src;\n"
      "    #10 release q;\n"
      "    #10 src = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_FALSE(q->is_forced);
  EXPECT_EQ(q->value.ToUint64(), 5u);
}

