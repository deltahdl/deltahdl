#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"

using namespace delta;

// --- ResolveWireWord ---

TEST(NetResolution, WireBothZero) {
  // 0 + 0 = 0
  Logic4Word a{0, 0};
  Logic4Word b{0, 0};
  auto r = ResolveWireWord(a, b);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WireBothOne) {
  // 1 + 1 = 1
  Logic4Word a{1, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWireWord(a, b);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WireConflict) {
  // 0 + 1 = x
  Logic4Word a{0, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWireWord(a, b);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(NetResolution, WireZAndValue) {
  // z + 1 = 1
  Logic4Word z{1, 1};
  Logic4Word one{1, 0};
  auto r = ResolveWireWord(z, one);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);

  // 0 + z = 0
  Logic4Word zero{0, 0};
  auto r2 = ResolveWireWord(zero, z);
  EXPECT_EQ(r2.aval, 0u);
  EXPECT_EQ(r2.bval, 0u);
}

TEST(NetResolution, WireBothZ) {
  // z + z = z
  Logic4Word z{1, 1};
  auto r = ResolveWireWord(z, z);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(NetResolution, WireXPropagates) {
  // x + 0 = x, x + 1 = x
  Logic4Word x{0, 1};
  Logic4Word zero{0, 0};
  auto r = ResolveWireWord(x, zero);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

// --- ResolveWandWord ---

TEST(NetResolution, WandZeroDominates) {
  // 0 & 1 = 0
  Logic4Word a{0, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWandWord(a, b);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WandBothOne) {
  // 1 & 1 = 1
  Logic4Word a{1, 0};
  Logic4Word b{1, 0};
  auto r = ResolveWandWord(a, b);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WandXWithOne) {
  // x & 1 = x
  Logic4Word x{0, 1};
  Logic4Word one{1, 0};
  auto r = ResolveWandWord(x, one);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(NetResolution, WandXWithZero) {
  // x & 0 = 0 (0 dominates)
  Logic4Word x{0, 1};
  Logic4Word zero{0, 0};
  auto r = ResolveWandWord(x, zero);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

// --- ResolveWorWord ---

TEST(NetResolution, WorOneDominates) {
  // 1 | 0 = 1
  Logic4Word a{1, 0};
  Logic4Word b{0, 0};
  auto r = ResolveWorWord(a, b);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WorBothZero) {
  // 0 | 0 = 0
  Logic4Word a{0, 0};
  Logic4Word b{0, 0};
  auto r = ResolveWorWord(a, b);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 0u);
}

TEST(NetResolution, WorXWithZero) {
  // x | 0 = x
  Logic4Word x{0, 1};
  Logic4Word zero{0, 0};
  auto r = ResolveWorWord(x, zero);
  EXPECT_EQ(r.aval, 0u);
  EXPECT_EQ(r.bval, 1u);
}

TEST(NetResolution, WorXWithOne) {
  // x | 1 = 1 (1 dominates)
  Logic4Word x{0, 1};
  Logic4Word one{1, 0};
  auto r = ResolveWorWord(x, one);
  EXPECT_EQ(r.aval, 1u);
  EXPECT_EQ(r.bval, 0u);
}

// --- Net::Resolve ---

TEST(NetResolution, ResolveSingleDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 42));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(NetResolution, ResolveMultipleDriversAgree) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // Two drivers both driving value 7.
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 7));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(NetResolution, ResolveMultipleDriversConflict) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // Two drivers: 0x0F and 0xF0 (conflict on all bits).
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));

  net.Resolve(arena);
  // Conflicting bits become x (bval=1, aval=0).
  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(NetResolution, ResolveWandNet) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;
  // 0xFF AND 0x0F = 0x0F
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(NetResolution, ResolveWorNet) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;
  // 0xF0 OR 0x0F = 0xFF
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xF0));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x0F));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(NetResolution, ResolveEmptyDrivers) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 99);
  Net net;
  net.resolved = var;
  // No drivers: value should remain unchanged.
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// --- Strength resolution (IEEE §28.12) ---

TEST(StrengthResolution, StrongerDriverWins) {
  Arena arena;
  auto* var = arena.Create<Variable>();
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
  auto* var = arena.Create<Variable>();
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
  auto* var = arena.Create<Variable>();
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
  auto* var = arena.Create<Variable>();
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
  auto* var = arena.Create<Variable>();
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
  auto* var = arena.Create<Variable>();
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

TEST(NetResolution, Tri0ResolvesToZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  // Single driver with z → resolves to 0 for tri0.
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0].aval = ~uint64_t{0};  // All z.
  drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0u);
}

TEST(NetResolution, Tri1ResolvesToOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  // Single driver with z → resolves to 1 for tri1.
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0].aval = ~uint64_t{0};
  drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0u);
}
