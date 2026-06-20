#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "helpers_logic4vec_z.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NetTypesIntro, WireValueFollowsSingleDriver) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x5A));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

TEST(NetTypesIntro, WireWithAllZDriversResolvesToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 4, 0xA);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeZVec(arena, 4));
  net.drivers.push_back(MakeZVec(arena, 4));

  net.Resolve(arena);
  EXPECT_TRUE(IsAllZ(var->value));
}

TEST(NetTypesIntro, WireDoesNotStoreValueWhenDriversReturnToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xC3));

  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64(), 0xC3u);

  net.drivers[0] = MakeZVec(arena, 8);
  net.Resolve(arena);
  EXPECT_TRUE(IsAllZ(var->value));
}

TEST(NetTypesIntro, TriregRetainsValueWhenAllDriversGoToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x7E));

  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64(), 0x7Eu);

  net.drivers[0] = MakeZVec(arena, 8);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0x7Eu);
}

TEST(NetTypesIntro, WireWithMultipleDriversCombinesValues) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0001));
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0b0001));

  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64() & 0xFu, 0b0001u);
}

TEST(NetTypesIntro, UndrivenBuiltinNetInitializesToZ) {
  SimFixture f;
  auto* net = f.ctx.CreateNet("w", NetType::kWire, 8);
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_TRUE(net->drivers.empty());
  EXPECT_TRUE(IsAllZ(net->resolved->value));
}

TEST(NetTypesIntro, ResolveWithEmptyDriversLeavesInitialZ) {
  SimFixture f;
  auto* net = f.ctx.CreateNet("w", NetType::kWire, 8);
  ASSERT_NE(net, nullptr);
  net->Resolve(f.arena);
  EXPECT_TRUE(IsAllZ(net->resolved->value));
}

TEST(NetTypesIntro, WandDoesNotStoreValueWhenDriversReturnToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xFF));

  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64() & 0xFFu, 0xFFu);

  net.drivers[0] = MakeZVec(arena, 8);
  net.drivers[1] = MakeZVec(arena, 8);
  net.Resolve(arena);
  EXPECT_TRUE(IsAllZ(var->value));
}

TEST(NetTypesIntro, TriregFollowsRemainingDriverWhenOneOfTwoGoesToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x33));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0x33));

  net.Resolve(arena);
  ASSERT_EQ(var->value.ToUint64() & 0xFFu, 0x33u);

  net.drivers[0] = MakeZVec(arena, 8);
  net.drivers[1] = MakeLogic4VecVal(arena, 8, 0x55);
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0x55u);
}

}  // namespace
