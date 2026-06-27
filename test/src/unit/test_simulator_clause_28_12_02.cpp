#include <gtest/gtest.h>

#include "common/arena.h"
#include "helpers_net_strength.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StrengthResolution, EqualStrengthConflictProducesX) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

TEST(StrengthCombine, EqualWeakOppositeValueProducesX) {
  StrengthSignal weak_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kWeak};
  StrengthSignal weak_zero{Val4::kV0, StrengthLevel::kWeak,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(weak_one, weak_zero);
  EXPECT_EQ(result.value, Val4::kX);
}

TEST(StrengthCombine, EqualStrengthConflictCarriesStrengthRange) {
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal pull_zero{Val4::kV0, StrengthLevel::kPull,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(pull_one, pull_zero);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
}

TEST(StrengthResolution, EqualSupplyConflictProducesX) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kSupply);
  AddDriver(arena, net, 1, 1, Strength::kSupply);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
}

TEST(StrengthResolution, EqualStrengthConflictPerBit) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 8);
  Net& net = sn.net;

  AddDriver(arena, net, 8, 0xF0, Strength::kStrong);
  AddDriver(arena, net, 8, 0x0F, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 0xFFu, 0xFFu);  // all bits x
  EXPECT_EQ(sn.var->value.words[0].bval & 0xFFu, 0xFFu);
}

TEST(StrengthCombine, AmbiguousSameRangePreserved) {
  StrengthSignal a{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kWeak};
  StrengthSignal b{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kWeak};
  auto result = CombineAmbiguous(a, b);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kWeak);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kWeak);
}

TEST(StrengthCombine, AmbiguousWidensToMaxPerSide) {
  StrengthSignal weak_x{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kWeak};
  StrengthSignal pull_x{Val4::kX, StrengthLevel::kPull, StrengthLevel::kPull};
  auto result = CombineAmbiguous(weak_x, pull_x);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
}

TEST(StrengthCombine, AmbiguousOppositeSidesUnion) {
  StrengthSignal pull_h{Val4::kX, StrengthLevel::kHighz, StrengthLevel::kPull};
  StrengthSignal weak_l{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kHighz};
  auto result = CombineAmbiguous(pull_h, weak_l);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kWeak);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kPull);
}

TEST(StrengthCombine, AmbiguousSupplyDominatesStrongPerSide) {
  StrengthSignal strong_x{Val4::kX, StrengthLevel::kStrong,
                          StrengthLevel::kStrong};
  StrengthSignal supply_x{Val4::kX, StrengthLevel::kSupply,
                          StrengthLevel::kSupply};
  auto result = CombineAmbiguous(strong_x, supply_x);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kSupply);
}

TEST(StrengthResolution, EqualStrengthPartialConflictPerBit) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 4);
  Net& net = sn.net;

  AddDriver(arena, net, 4, 0b1100, Strength::kStrong);
  AddDriver(arena, net, 4, 0b1010, Strength::kStrong);
  net.Resolve(arena);

  // bit3=1, bit2=x, bit1=x, bit0=0. Under Convention A an x bit sets aval, so
  // aval = 0b1110 (the known 1 at bit3 plus the two x bits), bval = 0b0110.
  EXPECT_EQ(sn.var->value.words[0].aval & 0xFu, 0b1110u);
  EXPECT_EQ(sn.var->value.words[0].bval & 0xFu, 0b0110u);
}

TEST(StrengthResolution,
     EqualStrengthConflictPopulatesAmbiguousResolvedStrength) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kPull);
  AddDriver(arena, net, 1, 1, Strength::kPull);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution,
     EqualSupplyConflictPopulatesAmbiguousResolvedStrength) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kSupply);
  AddDriver(arena, net, 1, 1, Strength::kSupply);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, EqualStrengthConflictLeavesLoAtHighz) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
}

TEST(StrengthCombine, AmbiguousThreeSignalsFoldPreservesRange) {
  StrengthSignal weak_x{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kWeak};
  StrengthSignal pull_x{Val4::kX, StrengthLevel::kPull, StrengthLevel::kPull};
  StrengthSignal strong_x{Val4::kX, StrengthLevel::kStrong,
                          StrengthLevel::kStrong};
  auto result = CombineAmbiguous(CombineAmbiguous(weak_x, pull_x), strong_x);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
}

TEST(StrengthResolution,
     EqualMediumConflictPopulatesAmbiguousResolvedStrength) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kMedium);
  AddDriver(arena, net, 1, 1, Strength::kMedium);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kMedium);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, EqualStrengthConflictOnTriNetPopulatesAmbiguous) {
  Arena arena;
  StrengthNet sn = MakeStrengthNet(arena, 1, NetType::kTri);
  Net& net = sn.net;

  AddDriver(arena, net, 1, 0, Strength::kStrong);
  AddDriver(arena, net, 1, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(sn.var->value.words[0].aval & 1u, 1u);  // x = (aval=1, bval=1)
  EXPECT_EQ(sn.var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

// Known-value-with-multi-level classification: only the value side carries
// a non-singleton range; the opposite side stays HiZ.
TEST(AmbiguousStrengthClass, KnownValueMultiLevelIsAmbiguous) {
  NetStrength ns;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kWeak;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_EQ(ns.s0_hi, Strength::kHighz);
  EXPECT_EQ(ns.s0_lo, Strength::kHighz);
}

// X-value classification: levels straddle both halves of the scale.
TEST(AmbiguousStrengthClass, XValueRangesOnBothSidesIsAmbiguous) {
  NetStrength ns;
  ns.s0_hi = Strength::kStrong;
  ns.s0_lo = Strength::kPull;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kPull;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_NE(ns.s0_hi, Strength::kHighz);
  EXPECT_NE(ns.s1_hi, Strength::kHighz);
}

// L-value classification: HiZ joined with a range in the strength0 part.
TEST(AmbiguousStrengthClass, LValueIsHighZJoinedWithStrengthZeroRange) {
  NetStrength ns;
  ns.s0_hi = Strength::kStrong;
  ns.s0_lo = Strength::kHighz;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_EQ(ns.s1_hi, Strength::kHighz);
  EXPECT_EQ(ns.s1_lo, Strength::kHighz);
}

// H-value classification: HiZ joined with a range in the strength1 part.
TEST(AmbiguousStrengthClass, HValueIsHighZJoinedWithStrengthOneRange) {
  NetStrength ns;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kHighz;
  EXPECT_TRUE(ns.IsAmbiguous());
  EXPECT_EQ(ns.s0_hi, Strength::kHighz);
  EXPECT_EQ(ns.s0_lo, Strength::kHighz);
}

// COMB-2 + COMB-3 via production CombineAmbiguousStrength: per-side hi widens
// to the maximum and per-side lo shrinks to the minimum, so the result's
// range on each side covers the ranges of both inputs.
TEST(AmbiguousNetStrengthCombine, WidensPerSideToCoverBothInputRanges) {
  NetStrength a;
  a.s0_hi = Strength::kWeak;
  a.s0_lo = Strength::kSmall;
  a.s1_hi = Strength::kPull;
  a.s1_lo = Strength::kWeak;
  NetStrength b;
  b.s0_hi = Strength::kPull;
  b.s0_lo = Strength::kMedium;
  b.s1_hi = Strength::kStrong;
  b.s1_lo = Strength::kMedium;

  NetStrength r = CombineAmbiguousStrength(a, b);

  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s0_lo, Strength::kSmall);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kMedium);
  EXPECT_TRUE(r.IsAmbiguous());
}

// COMB-2: combining two X-value (CLA-2) signals through production code
// yields a result that is still ambiguous on both sides.
TEST(AmbiguousNetStrengthCombine, XValueRangesProduceWiderXValueRange) {
  NetStrength a;
  a.s0_hi = Strength::kWeak;
  a.s0_lo = Strength::kSmall;
  a.s1_hi = Strength::kWeak;
  a.s1_lo = Strength::kSmall;
  NetStrength b;
  b.s0_hi = Strength::kStrong;
  b.s0_lo = Strength::kPull;
  b.s1_hi = Strength::kStrong;
  b.s1_lo = Strength::kPull;

  NetStrength r = CombineAmbiguousStrength(a, b);

  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s0_lo, Strength::kSmall);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kSmall);
  EXPECT_TRUE(r.IsAmbiguous());
}

// COMB-3: an L (CLA-3) and an H (CLA-4) input contribute their levels on
// opposite halves of the scale; the union covers both halves.
TEST(AmbiguousNetStrengthCombine, LAndHCombineToTwoSidedRange) {
  NetStrength l_signal;
  l_signal.s0_hi = Strength::kPull;
  l_signal.s0_lo = Strength::kHighz;
  NetStrength h_signal;
  h_signal.s1_hi = Strength::kPull;
  h_signal.s1_lo = Strength::kHighz;

  NetStrength r = CombineAmbiguousStrength(l_signal, h_signal);

  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
  EXPECT_TRUE(r.IsAmbiguous());
}

// Idempotency edge case for COMB-3: combining an ambiguous signal with
// itself returns an identical NetStrength. Per-side max/min on equal inputs
// collapses to the input.
TEST(AmbiguousNetStrengthCombine, SelfCombinationIsIdempotent) {
  NetStrength ns;
  ns.s0_hi = Strength::kPull;
  ns.s0_lo = Strength::kWeak;
  ns.s1_hi = Strength::kStrong;
  ns.s1_lo = Strength::kMedium;

  NetStrength r = CombineAmbiguousStrength(ns, ns);

  EXPECT_EQ(r.s0_hi, ns.s0_hi);
  EXPECT_EQ(r.s0_lo, ns.s0_lo);
  EXPECT_EQ(r.s1_hi, ns.s1_hi);
  EXPECT_EQ(r.s1_lo, ns.s1_lo);
  EXPECT_TRUE(r.IsAmbiguous());
}

// Edge case for COMB-3: combining an ambiguous signal whose lo is non-HiZ
// with a default (all-HiZ) NetStrength pushes the per-side lo down to HiZ
// while preserving the per-side hi. HiZ acts as the bottom of the scale
// for the min that defines the lo bound.
TEST(AmbiguousNetStrengthCombine, CombiningWithDefaultStretchesLoToHighz) {
  NetStrength narrow;
  narrow.s1_hi = Strength::kPull;
  narrow.s1_lo = Strength::kWeak;
  NetStrength empty;

  NetStrength r = CombineAmbiguousStrength(narrow, empty);

  EXPECT_EQ(r.s1_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
  EXPECT_EQ(r.s0_hi, Strength::kHighz);
  EXPECT_EQ(r.s0_lo, Strength::kHighz);
}

}  // namespace
