#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_net_strength.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(UserNettypeStrength, NonUserNettypeStillHonorsStrength) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = false;

  AddDriver(arena, net, 1, 1, Strength::kStrong);
  AddDriver(arena, net, 1, 0, Strength::kWeak);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.ToUint64(), 1u);
}

TEST(UserNettypeStrength, UserNettypeSingleDriverUsesValueOnly) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 1, 1, Strength::kHighz);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.ToUint64(), 1u);
}

TEST(UserNettypeStrength, UserNettypeIgnoresStrengthPerBit) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 4);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 4, 0b1100, Strength::kStrong);
  AddDriver(arena, net, 4, 0b1010, Strength::kWeak);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 0xFu, 0b1110u);
  EXPECT_EQ(sn.var->value.words[0].bval & 0xFu, 0b0110u);
}

TEST(UserNettypeStrength, UserNettypeIgnoresStrengthWithThreeDrivers) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 1, 0, Strength::kSupply);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  AddDriver(arena, net, 1, 0, Strength::kWeak);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

TEST(UserNettypeStrength, UserNettypeConflictKeepsNoStrengthLevels) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(NetStrengthDisjunction, UnambiguousDriversYieldUnambiguousNetStrength) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
}

TEST(NetStrengthDisjunction, ValueZeroDominantDriverRecordsStrengthOnSide0) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kHighz});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kHighz, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
}

TEST(NetStrengthDisjunction, AmbiguousNetStrengthIsRepresentable) {
  NetStrength ns;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kWeak;
  EXPECT_TRUE(ns.IsAmbiguous());

  NetStrength single;
  single.s0_hi = Strength::kPull;
  single.s0_lo = Strength::kPull;
  EXPECT_FALSE(single.IsAmbiguous());
}

TEST(UserNettypeStrength, RealSourceNettypeNetRecordsNoStrengthLevels) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic [7:0] byte_net;\n"
      "  byte_net x;\n"
      "  wire [7:0] y;\n"
      "  assign x = 8'hAB;\n"
      "  assign y = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* xvar = f.ctx.FindVariable("x");
  ASSERT_NE(xvar, nullptr);
  EXPECT_EQ(xvar->value.ToUint64(), 0xABu);

  auto* xnet = f.ctx.FindNet("x");
  ASSERT_NE(xnet, nullptr);
  EXPECT_TRUE(xnet->is_user_nettype);
  EXPECT_EQ(xnet->resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(xnet->resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(xnet->resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(xnet->resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(xnet->resolved_strength.IsAmbiguous());

  auto* ynet = f.ctx.FindNet("y");
  ASSERT_NE(ynet, nullptr);
  EXPECT_FALSE(ynet->is_user_nettype);
  EXPECT_EQ(ynet->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(ynet->resolved_strength.s1_lo, Strength::kStrong);
}

TEST(NetStrengthDisjunction, NetStrengthMutationTogglesIsAmbiguous) {
  NetStrength ns;
  EXPECT_FALSE(ns.IsAmbiguous());

  ns.s0_hi = Strength::kLarge;
  ns.s0_lo = Strength::kMedium;
  EXPECT_TRUE(ns.IsAmbiguous());

  ns.s0_lo = Strength::kLarge;
  EXPECT_FALSE(ns.IsAmbiguous());
}

TEST(NetStrengthDisjunction, VectorBitsResolvingUnalikeWidenTheReportedPair) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 2);
  Net& net = sn.net;

  net.drivers.push_back(MakeLogic4VecVal(arena, 2, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kWeak);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kWeak);
}

TEST(NetStrengthDisjunction, VectorBitsResolvingAlikeReportWhatOneBitDoes) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 2);
  Net& net = sn.net;

  net.drivers.push_back(MakeLogic4VecVal(arena, 2, 3));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(NetStrengthDisjunction, DriverOfUnknownValueRecordsItsLevelOnBothSides) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  auto drv = MakeLogic4Vec(arena, 1);
  drv.words[0].aval = 1;
  drv.words[0].bval = 1;
  net.drivers.push_back(drv);
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(NetStrengthDisjunction, NetWithNoDriverRecordsNoLevels) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
}

TEST(HighZStrengthResolution, LoneZeroDriverAtHighZResolvesToZ) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  AddDriver(arena, sn.net, 1, 0, Strength::kHighz);
  sn.net.Resolve(arena);

  EXPECT_EQ(sn.var->value.ToString(), "z");
}

TEST(HighZStrengthResolution, LoneOneDriverAtHighZResolvesToZ) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  AddDriver(arena, sn.net, 1, 1, Strength::kHighz);
  sn.net.Resolve(arena);

  EXPECT_EQ(sn.var->value.ToString(), "z");
}

TEST(HighZStrengthResolution, SourceDrivenHighZNetIsZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToString(), "z");
}

}  // namespace
