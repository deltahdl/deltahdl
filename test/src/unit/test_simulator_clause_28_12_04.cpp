#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StrengthResolution, WandResolvesSameStrengthConflictToAnd) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WorResolvesSameStrengthConflictToOr) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, TriandResolvesSameStrengthConflictToAnd) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTriand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, TriorResolvesSameStrengthConflictToOr) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrior;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WandBothOnesResolveToOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WorBothZerosResolveToZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WandStrongerDriverDominatesWeaker) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WandPerBitAnd) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1100));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1010));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0b1000u);
}

TEST(StrengthResolution, WorPerBitOr) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1100));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1010));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0b1110u);
}

TEST(StrengthResolution, WandZeroAndXResolvesToZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  auto x_val = MakeLogic4Vec(arena, 1);
  x_val.words[0].aval = 0;
  x_val.words[0].bval = 1;
  net.drivers.push_back(x_val);
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WorOneOrXResolvesToOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  auto x_val = MakeLogic4Vec(arena, 1);
  x_val.words[0].aval = 0;
  x_val.words[0].bval = 1;
  net.drivers.push_back(x_val);
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WorBothOnesResolveToOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WandBothZerosResolveToZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WandOneAndXResolvesToX) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  auto x_val = MakeLogic4Vec(arena, 1);
  x_val.words[0].aval = 0;
  x_val.words[0].bval = 1;
  net.drivers.push_back(x_val);
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 1u);
}

TEST(StrengthResolution, WorZeroOrXResolvesToX) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  auto x_val = MakeLogic4Vec(arena, 1);
  x_val.words[0].aval = 0;
  x_val.words[0].bval = 1;
  net.drivers.push_back(x_val);
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 1u);
}

TEST(StrengthResolution, WandConflictResultRecordsStrengthOnZeroSide) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
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
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
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
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  auto x_val = MakeLogic4Vec(arena, 1);
  x_val.words[0].aval = 0;
  x_val.words[0].bval = 1;
  net.drivers.push_back(x_val);
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, WorZeroOrXRecordsCombinedStrength) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  auto x_val = MakeLogic4Vec(arena, 1);
  x_val.words[0].aval = 0;
  x_val.words[0].bval = 1;
  net.drivers.push_back(x_val);
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kPull);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, WandLikeOnesRecordStrengthOnOneSide) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
}

TEST(StrengthResolution, WorLikeZerosRecordStrengthOnZeroSide) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
}

TEST(StrengthResolution, WandThreeDriversFoldToAnd) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, WorThreeDriversFoldToOr) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
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
