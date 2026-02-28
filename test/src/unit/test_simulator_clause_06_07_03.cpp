// §6.7.3: Initialization of nets with user-defined nettypes

#include <gtest/gtest.h>

#include <cstdint>
#include <functional>

#include "model_net_declaration.h"

using namespace delta;

namespace {

// §6.7.3: "The resolution function for any net of a user-defined nettype
//  shall be activated at time zero at least once."
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

// §6.7.3:
TEST(NetDecl, UserDefinedResolutionAtTimeZeroEvenNoDrivers) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  // No drivers added.

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

// §6.7.3: "The default initialization value for a net with a user-defined
//  nettype shall be the default value defined by the data type."
// NOTE: default for logic is x, not z.
TEST(NetDecl, UserDefinedNettypeDefaultIsDataTypeDefault) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  UserNettype nt;
  SetUserNettypeInitialValue(net, nt, arena);
  // logic default is x (aval=1, bval=1 → x in VPI convention... actually
  // let me just check the bits).
  EXPECT_EQ(ValOf(*var), kValX);
}

}  // namespace
