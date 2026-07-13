#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

TEST(ProceduralContinuousSchedulingSim,
     AssignCorrespondsToProcessSensitiveToSource) {
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

TEST(ProceduralContinuousSchedulingSim,
     ForceCorrespondsToProcessSensitiveToSource) {
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

TEST(ProceduralContinuousSchedulingSim,
     ExpressionChangeUsesCurrentValuesForTarget) {
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

// Claim 1 input form: a source element of the expression may be a net (driven
// by a continuous assignment, §4.9.1) rather than a variable. Net changes reach
// the process through a different scheduling path than variable writes, so the
// procedural continuous assignment must stay sensitive to them as well.
TEST(ProceduralContinuousSchedulingSim, ForceSensitiveToNetSourceElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  wire [7:0] w;\n"
      "  logic [7:0] q;\n"
      "  assign w = a;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    force q = w;\n"
      "    #10 a = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 42u);
  EXPECT_TRUE(q->is_forced);
}

// Claim 1 input form: the source-element form (a net driven by a continuous
// assignment) also applies to the `assign` procedural continuous assignment,
// not only to `force`. Net changes must re-propagate through the assign.
TEST(ProceduralContinuousSchedulingSim, AssignSensitiveToNetSourceElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  wire  [7:0] w;\n"
      "  logic [7:0] q;\n"
      "  assign w = a;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    assign q = w;\n"
      "    #10 a = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 42u);
  EXPECT_TRUE(q->is_forced);
}

// Claim 1 input form: `force` may determine a NET target (not only a variable).
// The forced net stays sensitive to its source, so a later source change
// reaches the net's resolved value.
TEST(ProceduralContinuousSchedulingSim, ForceTargetsNetSensitiveToSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  wire  [7:0] n;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    force n = a;\n"
      "    #10 a = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* n = f.ctx.FindNet("n");
  ASSERT_NE(n, nullptr);
  ASSERT_NE(n->resolved, nullptr);
  EXPECT_EQ(n->resolved->value.ToUint64(), 42u);
  EXPECT_TRUE(n->resolved->is_forced);
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

TEST(ProceduralContinuousSchedulingSim,
     AssignTracksCurrentValuesAcrossMultipleSources) {
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

// Claim 1 edge case: the process stays sensitive to the source, so the target
// tracks every subsequent source change, not just the first one.
TEST(ProceduralContinuousSchedulingSim,
     AssignStaysSensitiveAcrossRepeatedChanges) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, c;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    assign c = a;\n"
      "    #10 a = 8'd10;\n"
      "    #10 a = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 20u);
  EXPECT_TRUE(c->is_forced);
}

// Claim 2 followed by claim 1: after deassign deactivates the assign, a fresh
// procedural continuous assignment re-establishes a source-sensitive process.
TEST(ProceduralContinuousSchedulingSim, AssignReactivatesAfterDeassign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, c;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    assign c = a;\n"
      "    #10 deassign c;\n"
      "    #10 a = 8'd99;\n"
      "    #10 assign c = a;\n"
      "    #10 a = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 7u);
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
