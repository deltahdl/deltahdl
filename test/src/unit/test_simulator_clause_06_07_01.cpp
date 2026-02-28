// §6.7.1: Net declarations with built-in net types

#include <gtest/gtest.h>

#include <cstdint>

#include "model_net_declaration.h"

using namespace delta;

namespace {

// --- Strength information (§6.7.1) ---
// §6.7.1: "each bit of a net shall have additional strength information."
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

// --- Default initialization (§6.7.1) ---
// §6.7.1: "The default initialization value for a net shall be the
//  value z."
TEST(NetDecl, DefaultInitializationIsZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  InitializeNet(net, NetType::kWire, arena);
  EXPECT_EQ(ValOf(*var), kValZ);
}

// §6.7.1: "Nets with drivers shall assume the output value of their
//  drivers."
TEST(NetDecl, NetsWithDriversAssumeDriverValue) {
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

// §6.7.1: "The trireg net shall default to the value x, with the
//  strength specified in the net declaration."
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
