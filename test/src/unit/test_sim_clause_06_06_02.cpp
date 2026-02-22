// §6.6.2: Unresolved nets

#include <gtest/gtest.h>
#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

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

}  // namespace
