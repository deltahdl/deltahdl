#include <gtest/gtest.h>

#include <initializer_list>

#include "common/arena.h"
#include "helpers_net_strength.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// One (value, strength) pair for a width-1 net driver.
struct Width1Driver {
  uint64_t value;
  Strength strength;
};

// Builds a width-1 strength net, appends each given width-1 driver in order,
// resolves the net, and returns the StrengthNet so the caller can assert on the
// resolved strengths and backing variable. Centralizes the
// Arena/MakeStrengthNet/AddDriver/Resolve setup shared by the width-1
// StrengthResolution tests.
StrengthNet ResolveWidth1(Arena& arena,
                          std::initializer_list<Width1Driver> drivers) {
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;
  for (const Width1Driver& d : drivers) {
    AddDriver(arena, net, 1, d.value, d.strength);
  }
  net.Resolve(arena);
  return sn;
}

// Asserts the four resolved strength bounds of a width-1 net and that bit 0 of
// its backing variable holds an x. Canonical Convention A encodes x as
// (aval=1, bval=1). Centralizes the six-line assertion block shared by the
// ambiguous-result StrengthResolution tests.
void ExpectResolvedStrengthsAndX(const StrengthNet& sn, Strength s0_hi,
                                 Strength s0_lo, Strength s1_hi,
                                 Strength s1_lo) {
  const Net& net = sn.net;
  EXPECT_EQ(net.resolved_strength.s0_hi, s0_hi);
  EXPECT_EQ(net.resolved_strength.s0_lo, s0_lo);
  EXPECT_EQ(net.resolved_strength.s1_hi, s1_hi);
  EXPECT_EQ(net.resolved_strength.s1_lo, s1_lo);
  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

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
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kPull}, {1, Strength::kPull}, {0, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kPull, Strength::kWeak,
                              Strength::kPull, Strength::kLarge);
}

TEST(StrengthResolution, RuleAAndBTrimAmbigLoBoundsPerSideVuOne) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kStrong}, {1, Strength::kStrong}, {1, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kLarge,
                              Strength::kStrong, Strength::kWeak);
  EXPECT_TRUE(sn.net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, RuleBAtAmbigHiMinusOnePerSide) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kStrong}, {1, Strength::kStrong}, {0, Strength::kPull}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kPull,
                              Strength::kStrong, Strength::kStrong);
  EXPECT_TRUE(sn.net.resolved_strength.IsAmbiguous());
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
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kPull}, {1, Strength::kPull}, {0, Strength::kStrong}});
  Net& net = sn.net;

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(sn.var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, StrongestWeakerUnambigSelectedForRuleApplication) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(arena, {{0, Strength::kStrong},
                                         {1, Strength::kStrong},
                                         {0, Strength::kPull},
                                         {0, Strength::kWeak}});

  ExpectResolvedStrengthsAndX(sn, Strength::kStrong, Strength::kPull,
                              Strength::kStrong, Strength::kStrong);
}

TEST(StrengthResolution, RuleAAndBAtSmallestNonHighzSu) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kPull}, {1, Strength::kPull}, {0, Strength::kSmall}});

  ExpectResolvedStrengthsAndX(sn, Strength::kPull, Strength::kSmall,
                              Strength::kPull, Strength::kMedium);
}

// Rule a) at the top of the strength scale: an opposite-value supply-strength
// conflict yields an ambiguous range whose high end is supply; a weaker strong
// unambiguous driver leaves the supply level in place (rule a) while trimming
// the levels at or below strong (rule b). Exercises preservation of the maximum
// strength level through net.Resolve.
TEST(StrengthResolution, RuleAKeepsSupplyLevelAtTopOfScale) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kSupply}, {1, Strength::kSupply}, {0, Strength::kStrong}});

  // Unambiguous side (value 0) extends down to the unambiguous strong level;
  // the opposite side keeps only the supply level above strong.
  ExpectResolvedStrengthsAndX(sn, Strength::kSupply, Strength::kStrong,
                              Strength::kSupply, Strength::kSupply);
  EXPECT_TRUE(sn.net.resolved_strength.IsAmbiguous());
}

// Rule b) complete elimination on the value-1 branch: a stronger unambiguous
// driver of value 1 removes every level of a wholly weaker ambiguous signal,
// collapsing the result to an unambiguous value 1 at the driver's strength.
TEST(StrengthResolution, RuleBCompleteEliminationYieldsUnambigOne) {
  Arena arena;
  StrengthNet sn = ResolveWidth1(
      arena,
      {{0, Strength::kPull}, {1, Strength::kPull}, {1, Strength::kStrong}});
  Net& net = sn.net;

  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
  EXPECT_EQ(sn.var->value.ToUint64(), 1u);
}

}  // namespace
