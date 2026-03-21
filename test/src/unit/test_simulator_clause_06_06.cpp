#include <gtest/gtest.h>

#include "helpers_switch_network.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetTypes, UndrivenNetInitializesToZ) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  InitializeNet(net, NetType::kWire, arena);
  EXPECT_EQ(ValOf(*var), kValZ);
}

TEST(NetTypes, DrivenNetAssumesDriverValue) {
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

}  // namespace
