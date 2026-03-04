#include <gtest/gtest.h>

#include <cstdint>
#include <functional>

#include "helpers_switch_network.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetDecl, UserDefinedResolutionActivatedAtTimeZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  bool activated = false;
  UserNettype nt;
  nt.resolution = [&](Arena& a, const std::vector<Logic4Vec>&) -> Logic4Vec {
    activated = true;
    return MakeLogic4Vec(a, 1);
  };

  ActivateResolutionAtTimeZero(net, nt, arena);
  EXPECT_TRUE(activated);
}

TEST(NetDecl, UserDefinedResolutionAtTimeZeroEvenNoDrivers) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  bool activated = false;
  UserNettype nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    activated = true;
    EXPECT_TRUE(drivers.empty());
    return MakeLogic4Vec(a, 1);
  };

  ActivateResolutionAtTimeZero(net, nt, arena);
  EXPECT_TRUE(activated);
}

TEST(NetDecl, UserDefinedNettypeDefaultIsDataTypeDefault) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  UserNettype nt;
  SetUserNettypeInitialValue(net, nt, arena);

  EXPECT_EQ(ValOf(*var), kValX);
}

}
