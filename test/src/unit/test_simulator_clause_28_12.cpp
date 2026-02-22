// §28.12: Strengths and values of combined signals

#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

// --- Strength resolution (IEEE §28.12) ---
TEST(StrengthResolution, StrongerDriverWins) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // Driver A: drives 1 with strong strength.
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  // Driver B: drives 0 with weak strength.
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  net.Resolve(arena);
  // Strong 1 beats weak 0.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, WeakerDriverLoses) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // Driver A: drives 0 with supply strength.
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kSupply, Strength::kSupply});
  // Driver B: drives 1 with pull strength.
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kPull, Strength::kPull});
  net.Resolve(arena);
  // Supply 0 beats pull 1.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StrengthResolution, EqualStrengthConflictProducesX) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // Driver A: drives 0 with strong.
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  // Driver B: drives 1 with strong.
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);
  // Equal strength, different values → x.
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

TEST(StrengthResolution, HighzDriverIgnored) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // Driver A: drives 1 with weak.
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  // Driver B: drives z (highz).
  auto z_val = MakeLogic4Vec(arena, 1);
  z_val.words[0].aval = 1;
  z_val.words[0].bval = 1;
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.Resolve(arena);
  // Weak 1 wins over highz.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StrengthResolution, AllHighzProducesZ) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // Both drivers: z (highz).
  auto z_val = MakeLogic4Vec(arena, 1);
  z_val.words[0].aval = 1;
  z_val.words[0].bval = 1;
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.drivers.push_back(z_val);
  net.driver_strengths.push_back({Strength::kHighz, Strength::kHighz});
  net.Resolve(arena);
  // Both highz → z.
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

TEST(StrengthResolution, MultiBitMixed) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // Driver A: 0xFF with weak.
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.driver_strengths.push_back({Strength::kWeak, Strength::kWeak});
  // Driver B: 0x0F with strong.
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  net.Resolve(arena);
  // Bits 0-3: strong 1 (from B) beats weak 1 (from A) → 1.
  // Bits 4-7: strong 0 (from B) beats weak 1 (from A) → 0.
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

}  // namespace
