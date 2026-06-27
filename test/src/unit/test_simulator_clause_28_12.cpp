#include <gtest/gtest.h>

#include "common/arena.h"
#include "helpers_net_strength.h"
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

  // Bits 1,2 conflict -> x = (aval=1, bval=1); bit3=1, bit0=0 (Convention A).
  EXPECT_EQ(sn.var->value.words[0].aval & 0xFu, 0b1110u);
  EXPECT_EQ(sn.var->value.words[0].bval & 0xFu, 0b0110u);
}

TEST(UserNettypeStrength, UserNettypeResolveLeavesResolvedStrengthAtDefault) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 1, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
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

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

TEST(UserNettypeStrength, UserNettypeConflictKeepsNoStrengthLevels) {
  // Two equally strong, opposing drivers on a user-defined-nettype net. On an
  // ordinary net this conflict would populate a strength range (an ambiguous
  // strength); the nettype net must instead carry no strength levels at all,
  // resolving the conflict as a value only.
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  net.is_user_nettype = true;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  net.Resolve(arena);

  // Value resolves to x, the strengths having played no part in the outcome.
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);

  // No strength levels appear on either side of the scale.
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

TEST(NetStrengthDisjunction, NetStrengthMutationTogglesIsAmbiguous) {
  NetStrength ns;
  EXPECT_FALSE(ns.IsAmbiguous());

  ns.s0_hi = Strength::kLarge;
  ns.s0_lo = Strength::kMedium;
  EXPECT_TRUE(ns.IsAmbiguous());

  ns.s0_lo = Strength::kLarge;
  EXPECT_FALSE(ns.IsAmbiguous());
}

}  // namespace
