#include <gtest/gtest.h>

#include "common/arena.h"
#include "helpers_net_strength.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StrengthCombineAmbigUnambig, RuleAPreservesHighEndOfRange) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kSmall,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kWeak};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSmall);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kWeak);
}

TEST(StrengthCombineAmbigUnambig, RuleATrimsLowEndButKeepsHigh) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kPull,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz,
                       StrengthLevel::kStrong};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kStrong);
}

TEST(StrengthCombineAmbigUnambig, RuleBEliminatesAmbigAtOrBelowSu) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kStrong,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kWeak};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleBEliminatesAmbigAtExactlySu) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kPull,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleBSameValueMergeWithUnambig) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kWeak,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV0, StrengthLevel::kStrong,
                       StrengthLevel::kHighz};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kWeak);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RuleCFillsGapOnOppositeSide) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kPull,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{
      .value = Val4::kV1,
      .strength0_hi = StrengthLevel::kHighz,
      .strength1_hi = StrengthLevel::kSupply,
      .strength0_lo = StrengthLevel::kHighz,
      .strength1_lo = StrengthLevel::kSupply,
  };
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kPull);
}

TEST(StrengthCombineAmbigUnambig, RuleCFillsMultiLevelGap) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kWeak,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{
      .value = Val4::kV1,
      .strength0_hi = StrengthLevel::kHighz,
      .strength1_hi = StrengthLevel::kSupply,
      .strength0_lo = StrengthLevel::kHighz,
      .strength1_lo = StrengthLevel::kStrong,
  };
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kLarge);
}

TEST(StrengthCombineAmbigUnambig, RuleCDoesNotFillSameSideGap) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kWeak,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{
      .value = Val4::kV0,
      .strength0_hi = StrengthLevel::kSupply,
      .strength1_hi = StrengthLevel::kHighz,
      .strength0_lo = StrengthLevel::kStrong,
      .strength1_lo = StrengthLevel::kHighz,
  };
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, RulesAAndBApplyPerSide) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kPull,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kX, StrengthLevel::kStrong,
                       StrengthLevel::kStrong};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kStrong);
}

TEST(StrengthCombineAmbigUnambig, SupplyUnambigWipesAllAmbig) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kSupply,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz,
                       StrengthLevel::kSupply};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kHighz);
}

TEST(StrengthCombineAmbigUnambig, MirrorWithV1Unambig) {
  StrengthSignal unambig{Val4::kV1, StrengthLevel::kHighz,
                         StrengthLevel::kPull};
  StrengthSignal ambig{Val4::kV0, StrengthLevel::kStrong,
                       StrengthLevel::kHighz};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kPull);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
}

TEST(StrengthCombineAmbigUnambig, RuleCFillsGapOnOppositeSideMirror) {
  StrengthSignal unambig{Val4::kV1, StrengthLevel::kHighz,
                         StrengthLevel::kPull};
  StrengthSignal ambig{
      .value = Val4::kV0,
      .strength0_hi = StrengthLevel::kSupply,
      .strength1_hi = StrengthLevel::kHighz,
      .strength0_lo = StrengthLevel::kSupply,
      .strength1_lo = StrengthLevel::kHighz,
  };
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength0_lo, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kPull);
}

TEST(StrengthCombineAmbigUnambig, HighZUnambigPreservesEntireAmbig) {
  StrengthSignal unambig{Val4::kV0, StrengthLevel::kHighz,
                         StrengthLevel::kHighz};
  StrengthSignal ambig{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  auto result = CombineAmbiguousWithUnambiguous(unambig, ambig);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_lo, StrengthLevel::kSmall);
}

TEST(StrengthResolution, RuleAAndBTrimAmbigLoBoundsPerSide) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kPull);
  AddDriver(arena, net, 1, 1, Strength::kPull);
  AddDriver(arena, net, 1, 0, Strength::kWeak);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kWeak);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kLarge);
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

TEST(StrengthResolution, RuleAAndBTrimAmbigLoBoundsPerSideVuOne) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kWeak);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kLarge);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kWeak);
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, RuleBAtAmbigHiMinusOnePerSide) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  AddDriver(arena, net, 1, 0, Strength::kPull);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, AmbigUnambigPerBitIndependence) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 4);
  Net& net = sn.net;

  AddDriver(arena, net, 4, 0b1100, Strength::kPull);
  AddDriver(arena, net, 4, 0b0011, Strength::kPull);
  AddDriver(arena, net, 4, 0b1010, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.ToUint64() & 0xFu, 0b1010u);
}

TEST(StrengthResolution, RuleBCompleteEliminationProducesUnambigResult) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kPull);
  AddDriver(arena, net, 1, 1, Strength::kPull);
  AddDriver(arena, net, 1, 0, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(sn.var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, StrongestWeakerUnambigSelectedForRuleApplication) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  AddDriver(arena, net, 1, 0, Strength::kPull);
  AddDriver(arena, net, 1, 0, Strength::kWeak);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

TEST(StrengthResolution, RuleAAndBAtSmallestNonHighzSu) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kPull);
  AddDriver(arena, net, 1, 1, Strength::kPull);
  AddDriver(arena, net, 1, 0, Strength::kSmall);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kSmall);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kMedium);
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

// Rule a) at the top of the strength scale: an opposite-value supply-strength
// conflict yields an ambiguous range whose high end is supply; a weaker strong
// unambiguous driver leaves the supply level in place (rule a) while trimming
// the levels at or below strong (rule b). Exercises preservation of the maximum
// strength level through net.Resolve.
TEST(StrengthResolution, RuleAKeepsSupplyLevelAtTopOfScale) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kSupply);
  AddDriver(arena, net, 1, 1, Strength::kSupply);
  AddDriver(arena, net, 1, 0, Strength::kStrong);
  net.Resolve(arena);

  // Unambiguous side (value 0) extends down to the unambiguous strong level;
  // the opposite side keeps only the supply level above strong.
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kSupply);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

// Rule b) complete elimination on the value-1 branch: a stronger unambiguous
// driver of value 1 removes every level of a wholly weaker ambiguous signal,
// collapsing the result to an unambiguous value 1 at the driver's strength.
TEST(StrengthResolution, RuleBCompleteEliminationYieldsUnambigOne) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kPull);
  AddDriver(arena, net, 1, 1, Strength::kPull);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(sn.var->value.ToUint64(), 1u);
}

}  // namespace
