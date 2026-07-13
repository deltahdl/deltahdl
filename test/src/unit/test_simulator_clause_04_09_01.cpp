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

// The time-zero constant propagation §4.9.1 describes is not limited to a
// literal right-hand side: a parameter (§11.2.1) is equally a constant value,
// and the continuous-assignment process must propagate it into the target at
// time zero with no source-element change ever occurring.
TEST(ContinuousAssignSchedulingSim, ParameterConstantPropagatedAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 8'd17;\n"
      "  localparam Q = 8'd3;\n"
      "  logic [7:0] k;\n"
      "  assign k = P + Q;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("k")->value.ToUint64(), 20u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

// §4.9.1 closes by noting that the continuous-assignment process it describes
// also covers the implicit continuous assignments inferred from port
// connections (see §4.9.6). An input port connected to a constant outside
// expression is therefore evaluated at time zero, just like any explicit
// continuous assignment, propagating the constant into the local port net.
TEST(ContinuousAssignSchedulingSim,
     ImplicitPortAssignmentPropagatesConstantAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] p);\n"
      "endmodule\n"
      "module t;\n"
      "  child u(8'd7 + 8'd1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("u.p")->value.ToUint64(), 8u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

// The implicit continuous assignment inferred from a port connection is a real
// continuous-assignment process: it stays sensitive to the source elements of
// the outside expression and re-evaluates with current values whenever they
// change, exactly as the explicit form does.
TEST(ContinuousAssignSchedulingSim,
     ImplicitPortAssignmentTracksSourceElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] p);\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] src;\n"
      "  child u(src + 8'd1);\n"
      "  initial begin\n"
      "    src = 8'd10;\n"
      "    #10 src = 8'd100;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("u.p")->value.ToUint64(), 101u);
}

// An OUTPUT port connection is the other syntactic position from which §4.9.6
// infers an implicit continuous assignment: the driving side is the child's
// local port and the target is the outside net. §4.9.1 says this too is a
// continuous-assignment process, so a constant driven onto the child output
// reaches the parent net at time zero without any procedural activity.
TEST(ContinuousAssignSchedulingSim,
     ImplicitOutputPortAssignmentPropagatesConstantAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic [7:0] q);\n"
      "  assign q = 8'd77;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] w;\n"
      "  child u(w);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("w")->value.ToUint64(), 77u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

// The implicit output-port continuous assignment is likewise sensitive to its
// source: when the child recomputes its output net the parent connection
// tracks the new value with current-value semantics.
TEST(ContinuousAssignSchedulingSim,
     ImplicitOutputPortAssignmentTracksSourceElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] q);\n"
      "  assign q = a + 8'd1;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] src, dst;\n"
      "  child u(src, dst);\n"
      "  initial begin\n"
      "    src = 8'd10;\n"
      "    #10 src = 8'd50;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("dst")->value.ToUint64(), 51u);
}
