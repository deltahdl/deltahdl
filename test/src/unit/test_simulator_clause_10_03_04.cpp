#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DriveStrengthSim, DefaultStrengthDrivesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DriveStrengthSim, ExplicitStrengthDrivesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  assign (weak0, weak1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DriveStrengthSim, StrongerDriverWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  assign (strong0, strong1) w = 1'b1;\n"
      "  assign (weak0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DriveStrengthSim, HighzStrengthAllowsOtherDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b0;\n"
      "  assign (strong0, strong1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(DriveStrengthSim, NetDeclWithStrength) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire (weak0, weak1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DriveStrengthSim, NetDeclAssignStrengthReachesDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire (pull0, weak1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  ASSERT_EQ(net->driver_strengths.size(), 1u);
  EXPECT_EQ(net->driver_strengths[0].s0, Strength::kPull);
  EXPECT_EQ(net->driver_strengths[0].s1, Strength::kWeak);
}

TEST(DriveStrengthSim, NetDeclAssignDefaultStrength) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  ASSERT_EQ(net->driver_strengths.size(), 1u);
  EXPECT_EQ(net->driver_strengths[0].s0, Strength::kStrong);
  EXPECT_EQ(net->driver_strengths[0].s1, Strength::kStrong);
}

TEST(DriveStrengthSim, StandaloneAssignStrengthReachesDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  assign (pull0, weak1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  ASSERT_EQ(net->driver_strengths.size(), 1u);
  EXPECT_EQ(net->driver_strengths[0].s0, Strength::kPull);
  EXPECT_EQ(net->driver_strengths[0].s1, Strength::kWeak);
}

TEST(DriveStrengthSim, SupplyStrengthBeatsStrongDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  assign (supply0, supply1) w = 1'b1;\n"
      "  assign (strong0, strong1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DriveStrengthSim, PullStrengthBeatsWeakDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b1;\n"
      "  assign (weak0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
