#include <gtest/gtest.h>

#include "common/arena.h"
#include "model_strength.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StrengthCombine, StrongerSignalDominates) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal weak_zero{Val4::kV0, StrengthLevel::kWeak,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(strong_one, weak_zero);
  EXPECT_EQ(result.value, Val4::kV1);
}

TEST(StrengthCombine, LikeValueTakesGreaterStrength) {
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  auto result = CombineUnambiguous(pull_one, strong_one);
  EXPECT_EQ(result.value, Val4::kV1);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
}

TEST(StrengthCombine, IdenticalSignalsUnchanged) {
  StrengthSignal sig{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  auto result = CombineUnambiguous(sig, sig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
}

// R1 at the top of the driving-strength scale: supply-0 must dominate
// strong-1. Complements StrongerSignalDominates (strong vs weak) by exercising
// the highest two levels of the ordinal scale.
TEST(StrengthCombine, SupplyDominatesStrong) {
  StrengthSignal supply_zero{Val4::kV0, StrengthLevel::kSupply,
                             StrengthLevel::kHighz};
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  auto result = CombineUnambiguous(supply_zero, strong_one);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kSupply);
}

// R1 inside the charge-storage portion of the scale: medium-1 must dominate
// small-0. Confirms the dominance rule is purely ordinal and applies to the
// charge-storage strengths as well, not only to driving strengths.
TEST(StrengthCombine, ChargeStorageStrengthDominatesSmaller) {
  StrengthSignal medium_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kMedium};
  StrengthSignal small_zero{Val4::kV0, StrengthLevel::kSmall,
                            StrengthLevel::kHighz};
  auto result = CombineUnambiguous(medium_one, small_zero);
  EXPECT_EQ(result.value, Val4::kV1);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kMedium);
}

// R2 at the model level with more than two signals: three like-value signals
// of ascending strength must reduce to the common value carrying the maximum
// strength. Guards against a pairwise reduction that would forget the max
// strength after the first combine.
TEST(StrengthCombine, LikeValueThreeSignalsKeepMaxStrength) {
  StrengthSignal weak_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kWeak};
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  auto result = CombineUnambiguous(CombineUnambiguous(weak_one, pull_one),
                                   strong_one);
  EXPECT_EQ(result.value, Val4::kV1);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
}

TEST(StrengthCombine, EqualStrengthOppositeValueProducesX) {
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal pull_zero{Val4::kV0, StrengthLevel::kPull,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(pull_one, pull_zero);
  EXPECT_EQ(result.value, Val4::kX);
}

// R1 at the Net::Resolve level: a strong-1 driver must dominate a weak-0
// driver on a plain wire when both drive the same bit.
TEST(StrengthResolution, StrongerDriverWins) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// R1 symmetric: a supply-0 driver must dominate a pull-1 driver. Pairs a
// different strength gap from the StrongerDriverWins case to confirm the rule
// is ordinal, not tied to specific levels.
TEST(StrengthResolution, WeakerDriverLoses) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// R1 applies independently per bit: on a multi-bit net the strong driver wins
// only on the bits where its value differs, leaving the weak driver's bits
// intact where they agreed — verifying the per-bit dominance rule.
TEST(StrengthResolution, StrongerDriverWinsPerBit) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// R2 at Net::Resolve: two drivers carrying the same value at different
// strengths must still resolve to that common value. Net::Resolve only
// surfaces a Logic4Vec, so the strength-preservation half of R2 is covered at
// the model level; here we pin down that like-value drivers do not spuriously
// produce x when their strengths differ.
TEST(StrengthResolution, LikeValueDifferentStrengthsAgree) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// R3 at Net::Resolve: two drivers identical in both value and strength must
// resolve to that same value. Mirrors the StrengthCombine.IdenticalSignals
// test at the simulator runtime so an accidental divergence between the
// model and the live resolve path would be caught.
TEST(StrengthResolution, IdenticalDriversResolveSameValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// R1 with more than two drivers: a strong-1 among a pull-0 and a weak-0 must
// still win. Guards against a pairwise reduction that forgets the running
// dominant driver when a third driver is folded in.
TEST(StrengthResolution, ThreeDriversStrongestWins) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
