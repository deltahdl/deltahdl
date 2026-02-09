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
