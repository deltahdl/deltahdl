#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Creates the resolved Variable backing `net`, sets the net type and width, and
// returns the variable. Shared setup for the StrengthResolution tests.
Variable* SetupResolvedNet(Arena& arena, Net& net, NetType type,
                           uint32_t width = 1) {
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, width);
  net.type = type;
  net.resolved = var;
  return var;
}

// Pushes a driver with value `val` (width bits) and a uniform strength on both
// rails.
void PushDriver(Arena& arena, Net& net, uint64_t val, Strength strength,
                uint32_t width = 1) {
  net.drivers.push_back(MakeLogic4VecVal(arena, width, val));
  net.driver_strengths.push_back({strength, strength});
}

// Pushes a 1-bit X-valued driver with a uniform strength on both rails.
void PushXDriver(Arena& arena, Net& net, Strength strength) {
  auto x_val = MakeLogic4Vec(arena, 1);
  x_val.words[0].aval = 0;
  x_val.words[0].bval = 1;
  net.drivers.push_back(x_val);
  net.driver_strengths.push_back({strength, strength});
}

TEST(StrengthResolution, WandResolvesSameStrengthConflictToAnd) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushDriver(arena, net, 0, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WorResolvesSameStrengthConflictToOr) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWor);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushDriver(arena, net, 0, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, TriandResolvesSameStrengthConflictToAnd) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kTriand);

  PushDriver(arena, net, 1, Strength::kPull);
  PushDriver(arena, net, 0, Strength::kPull);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, TriorResolvesSameStrengthConflictToOr) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kTrior);

  PushDriver(arena, net, 1, Strength::kPull);
  PushDriver(arena, net, 0, Strength::kPull);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WandBothOnesResolveToOne) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushDriver(arena, net, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WorBothZerosResolveToZero) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWor);

  PushDriver(arena, net, 0, Strength::kStrong);
  PushDriver(arena, net, 0, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WandStrongerDriverDominatesWeaker) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushDriver(arena, net, 0, Strength::kWeak);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WandPerBitAnd) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand, 4);

  PushDriver(arena, net, 0b1100, Strength::kStrong, 4);
  PushDriver(arena, net, 0b1010, Strength::kStrong, 4);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0b1000u);
}

TEST(StrengthResolution, WorPerBitOr) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWor, 4);

  PushDriver(arena, net, 0b1100, Strength::kStrong, 4);
  PushDriver(arena, net, 0b1010, Strength::kStrong, 4);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0b1110u);
}

TEST(StrengthResolution, WandZeroAndXResolvesToZero) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 0, Strength::kStrong);
  PushXDriver(arena, net, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WorOneOrXResolvesToOne) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWor);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushXDriver(arena, net, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WorBothOnesResolveToOne) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWor);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushDriver(arena, net, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WandBothZerosResolveToZero) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 0, Strength::kStrong);
  PushDriver(arena, net, 0, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WandOneAndXResolvesToX) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushXDriver(arena, net, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 1u);
}

TEST(StrengthResolution, WorZeroOrXResolvesToX) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWor);

  PushDriver(arena, net, 0, Strength::kStrong);
  PushXDriver(arena, net, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 1u);
}

TEST(StrengthResolution, WandConflictResultRecordsStrengthOnZeroSide) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushDriver(arena, net, 0, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, WorConflictResultRecordsStrengthOnOneSide) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWor);

  PushDriver(arena, net, 1, Strength::kPull);
  PushDriver(arena, net, 0, Strength::kPull);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, WandOneAndXRecordsCombinedStrength) {
  Arena arena;
  Net net;
  SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushXDriver(arena, net, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, WorZeroOrXRecordsCombinedStrength) {
  Arena arena;
  Net net;
  SetupResolvedNet(arena, net, NetType::kWor);

  PushDriver(arena, net, 0, Strength::kPull);
  PushXDriver(arena, net, Strength::kPull);
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, WandLikeOnesRecordStrengthOnOneSide) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushDriver(arena, net, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
}

TEST(StrengthResolution, WorLikeZerosRecordStrengthOnZeroSide) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWor);

  PushDriver(arena, net, 0, Strength::kStrong);
  PushDriver(arena, net, 0, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
}

TEST(StrengthResolution, WandThreeDriversFoldToAnd) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWand);

  PushDriver(arena, net, 1, Strength::kStrong);
  PushDriver(arena, net, 1, Strength::kStrong);
  PushDriver(arena, net, 0, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WorThreeDriversFoldToOr) {
  Arena arena;
  Net net;
  auto* var = SetupResolvedNet(arena, net, NetType::kWor);

  PushDriver(arena, net, 0, Strength::kStrong);
  PushDriver(arena, net, 0, Strength::kStrong);
  PushDriver(arena, net, 1, Strength::kStrong);
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(WiredLogicAmbig, AndPairwiseAcrossStrengthRanges) {
  NetStrength a;
  a.s0_lo = Strength::kPull;
  a.s0_hi = Strength::kStrong;
  NetStrength b;
  b.s1_lo = Strength::kLarge;
  b.s1_hi = Strength::kPull;

  auto r = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);

  EXPECT_EQ(r.s0_lo, Strength::kPull);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

TEST(WiredLogicAmbig, OrPairwiseAcrossStrengthRanges) {
  NetStrength a;
  a.s0_lo = Strength::kPull;
  a.s0_hi = Strength::kStrong;
  NetStrength b;
  b.s1_lo = Strength::kLarge;
  b.s1_hi = Strength::kPull;

  auto r = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kOr);

  EXPECT_EQ(r.s0_lo, Strength::kPull);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kPull);
  EXPECT_EQ(r.s1_hi, Strength::kPull);
}

TEST(WiredLogicAmbig, LikeValuesKeepSingleSideUnionedRange) {
  NetStrength a;
  a.s1_lo = Strength::kWeak;
  a.s1_hi = Strength::kPull;
  NetStrength b;
  b.s1_lo = Strength::kLarge;
  b.s1_hi = Strength::kStrong;

  auto r_and = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);
  auto r_or = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kOr);

  EXPECT_EQ(r_and.s0_hi, Strength::kHighz);
  EXPECT_EQ(r_and.s1_lo, Strength::kLarge);
  EXPECT_EQ(r_and.s1_hi, Strength::kStrong);
  EXPECT_EQ(r_or.s0_hi, Strength::kHighz);
  EXPECT_EQ(r_or.s1_lo, Strength::kLarge);
  EXPECT_EQ(r_or.s1_hi, Strength::kStrong);
}

TEST(WiredLogicAmbig, UnambigInputsAgreeWithPerPairRule) {
  NetStrength a;
  a.s0_lo = Strength::kStrong;
  a.s0_hi = Strength::kStrong;
  NetStrength b;
  b.s1_lo = Strength::kStrong;
  b.s1_hi = Strength::kStrong;

  auto r_and = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);
  auto r_or = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kOr);

  EXPECT_EQ(r_and.s0_lo, Strength::kStrong);
  EXPECT_EQ(r_and.s0_hi, Strength::kStrong);
  EXPECT_EQ(r_and.s1_hi, Strength::kHighz);
  EXPECT_EQ(r_or.s1_lo, Strength::kStrong);
  EXPECT_EQ(r_or.s1_hi, Strength::kStrong);
  EXPECT_EQ(r_or.s0_hi, Strength::kHighz);
}

TEST(WiredLogicAmbig, AndProducesDualSidedRange) {
  NetStrength a;
  a.s0_lo = Strength::kPull;
  a.s0_hi = Strength::kPull;
  a.s1_lo = Strength::kStrong;
  a.s1_hi = Strength::kStrong;
  NetStrength b;
  b.s1_lo = Strength::kPull;
  b.s1_hi = Strength::kPull;

  auto r = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);

  EXPECT_EQ(r.s0_lo, Strength::kPull);
  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kStrong);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_FALSE(r.IsAmbiguous());
}

TEST(WiredLogicAmbig, EmptyInputProducesEmptyRange) {
  NetStrength a;
  NetStrength b;
  b.s0_lo = Strength::kPull;
  b.s0_hi = Strength::kPull;

  auto r = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);

  EXPECT_EQ(r.s0_hi, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
}

}  // namespace
