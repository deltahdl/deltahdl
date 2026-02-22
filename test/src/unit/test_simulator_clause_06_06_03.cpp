// §6.6.3: Wired nets

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"
#include <gtest/gtest.h>

using namespace delta;

namespace {

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

TEST(NetResolution, ResolveWandNet) {
  Arena arena;
  auto *var = arena.Create<Variable>();
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
  auto *var = arena.Create<Variable>();
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

} // namespace
