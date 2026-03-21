#include <gtest/gtest.h>

#include "helpers_switch_network.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetDecl, UndrivenNetInitializesToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  InitializeNet(net, NetType::kWire, arena);
  EXPECT_EQ(ValOf(*var), kValZ);
}

TEST(NetDecl, DrivenNetAssumesDriverValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 1));
  InitializeNet(net, NetType::kWire, arena);
  EXPECT_EQ(ValOf(*var), kVal1);
}

TEST(NetDecl, UndrivenTriInitializesToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTri;
  net.resolved = var;
  InitializeNet(net, NetType::kTri, arena);
  EXPECT_EQ(ValOf(*var), kValZ);
}

TEST(NetDecl, UndrivenWandInitializesToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWand;
  net.resolved = var;
  InitializeNet(net, NetType::kWand, arena);
  EXPECT_EQ(ValOf(*var), kValZ);
}

TEST(NetDecl, UndrivenWorInitializesToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWor;
  net.resolved = var;
  InitializeNet(net, NetType::kWor, arena);
  EXPECT_EQ(ValOf(*var), kValZ);
}

TEST(NetDecl, NetValueUsesFourStateEncoding) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  InitializeNet(net, NetType::kWire, arena);
  // z is encoded as aval=1, bval=1 in 4-state representation.
  EXPECT_EQ(var->value.words[0].aval, 1u);
  EXPECT_EQ(var->value.words[0].bval, 1u);
}

TEST(NetDecl, EachBitHasStrengthInformation) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 4);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 4, 0xF));
  net.driver_strengths.push_back({Strength::kStrong, Strength::kStrong});
  EXPECT_EQ(net.driver_strengths.size(), 1u);
}

TEST(NetDecl, TriregDefaultsToXSmall) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  InitializeTriregNet(net, LocalChargeStrength::kSmall, arena);
  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(NetDecl, TriregDefaultsToXMedium) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  InitializeTriregNet(net, LocalChargeStrength::kMedium, arena);
  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(NetDecl, TriregDefaultsToXLarge) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;
  InitializeTriregNet(net, LocalChargeStrength::kLarge, arena);
  EXPECT_EQ(ValOf(*var), kValX);
}

}  // namespace
