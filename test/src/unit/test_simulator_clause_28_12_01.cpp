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

TEST(StrengthCombine, LikeValueThreeSignalsKeepMaxStrength) {
  StrengthSignal weak_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kWeak};
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  auto result =
      CombineUnambiguous(CombineUnambiguous(weak_one, pull_one), strong_one);
  EXPECT_EQ(result.value, Val4::kV1);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
}

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

TEST(StrengthResolution, IdenticalDriversPreserveResolvedStrength) {
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

  EXPECT_EQ(net.resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s0_lo, Strength::kPull);
  EXPECT_EQ(net.resolved_strength.s1_hi, Strength::kHighz);
  EXPECT_EQ(net.resolved_strength.s1_lo, Strength::kHighz);
  EXPECT_FALSE(net.resolved_strength.IsAmbiguous());
}

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

TEST(StrengthResolution, HighzDriverIgnored) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});

  auto z_val = MakeLogic4Vec(arena, 1);
  z_val.words[0].aval = 1;
  z_val.words[0].bval = 1;
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.Resolve(arena);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, AllHighzProducesZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  auto z_val = MakeLogic4Vec(arena, 1);
  z_val.words[0].aval = 1;
  z_val.words[0].bval = 1;
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.Resolve(arena);

  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

}  // namespace
