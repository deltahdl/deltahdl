#include <gtest/gtest.h>

#include "common/arena.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StrengthResolution, EqualStrengthConflictProducesX) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
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
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

TEST(StrengthResolution, EqualStrengthConflictPerBit) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFFu, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFFu, 0xFFu);
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
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1100));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b1010));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 0xFu, 0b1000u);
  EXPECT_EQ(var->value.words[0].bval & 0xFu, 0b0110u);
}

TEST(StrengthResolution, EqualStrengthConflictPopulatesAmbiguousResolvedStrength) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kPull);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, EqualSupplyConflictPopulatesAmbiguousResolvedStrength) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, EqualStrengthConflictLeavesLoAtHighz) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
}

TEST(StrengthCombine, AmbiguousThreeSignalsFoldPreservesRange) {
  StrengthSignal weak_x{Val4::kX, StrengthLevel::kWeak, StrengthLevel::kWeak};
  StrengthSignal pull_x{Val4::kX, StrengthLevel::kPull, StrengthLevel::kPull};
  StrengthSignal strong_x{Val4::kX, StrengthLevel::kStrong,
                          StrengthLevel::kStrong};
  auto result =
      CombineAmbiguous(CombineAmbiguous(weak_x, pull_x), strong_x);
  EXPECT_EQ(result.value, Val4::kX);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
}

TEST(StrengthResolution, EqualMediumConflictPopulatesAmbiguousResolvedStrength) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kMedium, Strength::kMedium});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kMedium, Strength::kMedium});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kMedium);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kMedium);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

TEST(StrengthResolution, EqualStrengthConflictOnTriNetPopulatesAmbiguous) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_TRUE(net.resolved_strength.IsAmbiguous());
}

}
