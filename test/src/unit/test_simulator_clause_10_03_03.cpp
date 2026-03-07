#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §10.3.3: Single delay on continuous assignment delays the update.

TEST(SimClause100303, SingleDelayDefersAssignment) {
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

// §10.3.3: Rise/fall delay — rising transition uses rise delay.

TEST(SimClause100303, RiseFallDelayUsesRiseForZeroToOne) {
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

// §10.3.3: Rise/fall delay — falling transition uses fall delay.

TEST(SimClause100303, RiseFallDelayUsesFallForOneToZero) {
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
  // Rise at t=5, then fall at t=20+10=30.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 30u);
}

// §10.3.3: Three-value delay — turn-off delay for transition to z.

TEST(SimClause100303, ThreeDelayTurnoff) {
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
  // Rise at t=5, then turn-off at t=20+15=35.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 35u);
}

// §10.3.3: No delay — assignment happens at time 0.

TEST(SimClause100303, NoDelayAssignsImmediately) {
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

// §10.3.3: Two-value delay on vector — smaller of rise/fall for x→known.

TEST(SimClause100303, TwoDelayVectorUsesMinForXToKnown) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign #(5, 10) y = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
  // x→1 transition: min(rise=5, fall=10) = 5
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}

}  // namespace
