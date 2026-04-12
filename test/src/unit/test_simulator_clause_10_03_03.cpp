#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AssignmentDelaySim, SingleDelayDefersAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign #10 y = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(AssignmentDelaySim, RiseFallDelayUsesRiseForZeroToOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire y;\n"
      "  assign #(5, 10) y = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}

TEST(AssignmentDelaySim, RiseFallDelayUsesFallForOneToZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  assign #(5, 10) y = src;\n"
      "  initial begin\n"
      "    src = 1'b1;\n"
      "    #20 src = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 30u);
}

TEST(AssignmentDelaySim, ThreeDelayTurnoff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  assign #(5, 10, 15) y = src;\n"
      "  initial begin\n"
      "    src = 1'b1;\n"
      "    #20 src = 1'bz;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 35u);
}

TEST(AssignmentDelaySim, NoDelayAssignsImmediately) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign y = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(AssignmentDelaySim, TwoDelayVectorXToKnownUsesRise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5) y = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
  // X->known on a vector is "all other transitions" -> rise delay (20).
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 20u);
}

TEST(AssignmentDelaySim, VectorNonzeroToNonzeroUsesRise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5) y = src;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    #50 src = 8'h01;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x01u);
  // FF->01 is nonzero->nonzero -> rise delay (20), scheduled at t=50.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 70u);
}

TEST(AssignmentDelaySim, VectorNonzeroToZeroUsesFall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5) y = src;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    #50 src = 8'h00;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  // FF->00 is nonzero->zero -> fall delay (5), scheduled at t=50.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 55u);
}

TEST(AssignmentDelaySim, NetDeclSingleDelayApplied) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire #10 w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(AssignmentDelaySim, VectorNetDeclDelayWholeVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire #5 [7:0] w = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}

TEST(AssignmentDelaySim, InertialDelayCancelsPending) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  assign #10 y = src;\n"
      "  initial begin\n"
      "    src = 1'b1;\n"
      "    #5 src = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  // Inertial: src=1 at t=0 schedules y=1 at t=10, but src=0 at t=5
  // cancels that and schedules y=0 at t=15.
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 15u);
}

TEST(AssignmentDelaySim, InertialDelayNoIntermediateGlitch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  logic [7:0] count;\n"
      "  assign #10 y = src;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    src = 1'b1;\n"
      "    #5 src = 1'b0;\n"
      "    #20 count = count;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  // With inertial delay, y should never transition to 1.
  // The final value should be 0.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

}  // namespace
