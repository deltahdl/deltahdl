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

}
