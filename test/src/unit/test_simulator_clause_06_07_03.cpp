#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <vector>

#include "common/arena.h"
#include "helpers_switch_network.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

using ResolutionFn =
    std::function<Logic4Vec(Arena&, const std::vector<Logic4Vec>&)>;

struct UserNettypeInit {
  ResolutionFn resolution;
};

static bool ResolveUserDefinedNetInit(Net& net, const UserNettypeInit& nettype,
                                      Arena& arena) {
  if (nettype.resolution) {
    Logic4Vec result = nettype.resolution(arena, net.drivers);
    net.resolved->value = result;
  }
  return true;
}

static Variable* MakeVar(Arena& arena, uint32_t width) {
  auto* v = arena.Create<Variable>();
  v->value = MakeLogic4Vec(arena, width);
  return v;
}

// §6.7.3: Resolution function activated at time zero at least once.
TEST(NettypeInitialization, ResolutionActivatedAtTimeZero) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  bool activated = false;
  UserNettypeInit nt;
  nt.resolution = [&](Arena& a, const std::vector<Logic4Vec>&) -> Logic4Vec {
    activated = true;
    return MakeLogic4Vec(a, 1);
  };

  ResolveUserDefinedNetInit(net, nt, arena);
  EXPECT_TRUE(activated);
}

// §6.7.3: Resolution function activated at time zero even with no drivers.
TEST(NettypeInitialization, ResolutionAtTimeZeroEvenNoDrivers) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  bool activated = false;
  UserNettypeInit nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    activated = true;
    EXPECT_TRUE(drivers.empty());
    return MakeLogic4Vec(a, 1);
  };

  ResolveUserDefinedNetInit(net, nt, arena);
  EXPECT_TRUE(activated);
}

// §6.7.3: Default initialization is data type default (x for logic).
TEST(NettypeInitialization, DefaultIsDataTypeDefault) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  EXPECT_EQ(ValOf(*var), kValX);
}

// §6.7.3: Multi-bit net defaults to all-x.
TEST(NettypeInitialization, MultiBitDefaultIsAllX) {
  Arena arena;
  auto* var = MakeVar(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  // Every bit should be x (aval=1, bval=1).
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

// §6.7.3: Initial value is set before time-zero resolution call.
TEST(NettypeInitialization, InitialValueSetBeforeResolution) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  uint8_t value_seen_by_resolution = 0xFF;
  UserNettypeInit nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& /*drivers*/) -> Logic4Vec {
    // Capture the resolved value at the time the resolution function is called.
    value_seen_by_resolution = ValOf(*var);
    return MakeLogic4Vec(a, 1);
  };

  ResolveUserDefinedNetInit(net, nt, arena);
  // The initial value (x) must have been set before resolution was invoked.
  EXPECT_EQ(value_seen_by_resolution, kValX);
}

// §6.7.3: Resolution with empty drivers produces the initial resolved value.
TEST(NettypeInitialization, ResolutionWithEmptyDriversSetsResolvedValue) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  UserNettypeInit nt;
  nt.resolution = [](Arena& a,
                     const std::vector<Logic4Vec>& drivers) -> Logic4Vec {
    EXPECT_TRUE(drivers.empty());
    // Resolution function returns 0 for empty drivers.
    return MakeLogic4VecVal(a, 1, 0);
  };

  ResolveUserDefinedNetInit(net, nt, arena);
  EXPECT_EQ(ValOf(*var), kVal0);
}

// §6.7.3: Without resolution function, net retains data type default.
TEST(NettypeInitialization, NoResolutionRetainsDefault) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  UserNettypeInit nt;
  ResolveUserDefinedNetInit(net, nt, arena);

  EXPECT_EQ(ValOf(*var), kValX);
}

// §6.7.3: Default is x (not z) — distinguish from built-in net default.
TEST(NettypeInitialization, DefaultIsXNotZ) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  EXPECT_NE(ValOf(*var), kValZ);
  EXPECT_EQ(ValOf(*var), kValX);
}

// §6.7.3: Resolution function return value overwrites the default x.
TEST(NettypeInitialization, ResolutionOverwritesDefault) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  EXPECT_EQ(ValOf(*var), kValX);

  UserNettypeInit nt;
  nt.resolution = [](Arena& a,
                     const std::vector<Logic4Vec>& /*drivers*/) -> Logic4Vec {
    return MakeLogic4VecVal(a, 1, 1);
  };

  ResolveUserDefinedNetInit(net, nt, arena);
  EXPECT_EQ(ValOf(*var), kVal1);
}
