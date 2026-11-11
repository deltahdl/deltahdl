#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DriveStrengthSim, StrongerDriverWins) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  assign (strong0, strong1) w = 1'b1;\n"
      "  assign (weak0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DriveStrengthSim, HighzStrengthAllowsOtherDriver) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b0;\n"
      "  assign (strong0, strong1) w = 1'b0;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(DriveStrengthSim, NetDeclWithStrength) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire (weak0, weak1) w = 1'b1;\n"
      "endmodule\n",
      f, "w");
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

TEST(DriveStrengthSim, StandaloneAssignDefaultStrengthReachesDriver) {
  ExpectSingleDriverStrength(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      Strength::kStrong, Strength::kStrong);
}

TEST(DriveStrengthSim, SupplyStrengthReachesDriver) {
  ExpectSingleDriverStrength(
      "module t;\n"
      "  wire w;\n"
      "  assign (supply0, supply1) w = 1'b1;\n"
      "endmodule\n",
      Strength::kSupply, Strength::kSupply);
}

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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  assign (supply0, supply1) w = 1'b1;\n"
      "  assign (strong0, strong1) w = 1'b0;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DriveStrengthSim, PullStrengthBeatsWeakDriver) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  assign (pull0, pull1) w = 1'b1;\n"
      "  assign (weak0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DriveStrengthSim, EitherOrderOfTheTwoStrengthsDrivesTheSame) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a = 1, b = 0;\n"
                       "  wire w1, w2;\n"
                       "  assign (pull0, strong1) w1 = a;\n"
                       "  assign (weak0, weak1) w1 = b;\n"
                       "  assign (strong1, pull0) w2 = a;\n"
                       "  assign (weak0, weak1) w2 = b;\n"
                       "  initial begin\n"
                       "    #1 $display(\"%b %v %b %v\", w1, w1, w2, w2);\n"
                       "    a = 0; b = 1;\n"
                       "    #1 $display(\"%b %v %b %v\", w1, w1, w2, w2);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 St1 1 St1\n0 Pu0 0 Pu0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthSim, AStrengthAppliesToEveryAssignmentOfItsList) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic x = 1, y = 0;\n"
                       "  wire p, q;\n"
                       "  assign (weak0, weak1) p = x, q = y;\n"
                       "  initial #1 $display(\"%v %v\", p, q);\n"
                       "endmodule\n",
                       f),
            "We1 We0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
