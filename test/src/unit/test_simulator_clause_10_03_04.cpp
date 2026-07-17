#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborates and lowers `src`, then asserts that net `w` carries exactly one
// driver whose strengths match (expected0, expected1).
static void ExpectSingleDriverStrength(const char* src, Strength expected0,
                                       Strength expected1) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* net = f.ctx.FindNet("w");
  ASSERT_NE(net, nullptr);
  ASSERT_EQ(net->driver_strengths.size(), 1u);
  EXPECT_EQ(net->driver_strengths[0].s0, expected0);
  EXPECT_EQ(net->driver_strengths[0].s1, expected1);
}

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
  ExpectSingleDriverStrength(
      "module t;\n"
      "  wire (pull0, weak1) w = 1'b1;\n"
      "endmodule\n",
      Strength::kPull, Strength::kWeak);
}

TEST(DriveStrengthSim, NetDeclAssignDefaultStrength) {
  ExpectSingleDriverStrength(
      "module t;\n"
      "  wire w = 1'b0;\n"
      "endmodule\n",
      Strength::kStrong, Strength::kStrong);
}

TEST(DriveStrengthSim, StandaloneAssignStrengthReachesDriver) {
  ExpectSingleDriverStrength(
      "module t;\n"
      "  wire w;\n"
      "  assign (pull0, weak1) w = 1'b1;\n"
      "endmodule\n",
      Strength::kPull, Strength::kWeak);
}

// §10.3.4: when a continuous assignment carries no drive strength, the strength
// shall default to (strong1, strong0). The net-declaration form is checked
// above; this covers the other syntactic position §10.3.4 names -- a
// stand-alone `assign` statement -- confirming the lowerer applies the same
// default there.
TEST(DriveStrengthSim, StandaloneAssignDefaultStrengthReachesDriver) {
  ExpectSingleDriverStrength(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      Strength::kStrong, Strength::kStrong);
}

// §10.3.4: the drive strength shall be simulated as specified. The supply level
// (parser encoding 5) reaches the lowered driver as Strength::kSupply. This
// covers a strength level the pull/weak/strong reaches-driver tests do not
// observe directly, exercising ParserStrToStrength's supply case.
TEST(DriveStrengthSim, SupplyStrengthReachesDriver) {
  ExpectSingleDriverStrength(
      "module t;\n"
      "  wire w;\n"
      "  assign (supply0, supply1) w = 1'b1;\n"
      "endmodule\n",
      Strength::kSupply, Strength::kSupply);
}

// The highz level (encoding 1) is legal when paired with a non-highz strength
// (an all-highz pair is illegal per §10.3.4). It reaches the driver as
// Strength::kHighz on the 0 side while the 1 side keeps its strong drive,
// exercising ParserStrToStrength's highz case at a driver.
TEST(DriveStrengthSim, HighzStrengthReachesDriver) {
  ExpectSingleDriverStrength(
      "module t;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b1;\n"
      "endmodule\n",
      Strength::kHighz, Strength::kStrong);
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
