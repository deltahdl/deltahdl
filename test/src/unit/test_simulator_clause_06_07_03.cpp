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

TEST(NettypeInitialization, DefaultIsDataTypeDefault) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(NettypeInitialization, MultiBitDefaultIsAllX) {
  Arena arena;
  auto* var = MakeVar(arena, 8);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(NettypeInitialization, InitialValueSetBeforeResolution) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  uint8_t value_seen_by_resolution = 0xFF;
  UserNettypeInit nt;
  nt.resolution = [&](Arena& a,
                      const std::vector<Logic4Vec>& ) -> Logic4Vec {

    value_seen_by_resolution = ValOf(*var);
    return MakeLogic4Vec(a, 1);
  };

  ResolveUserDefinedNetInit(net, nt, arena);

  EXPECT_EQ(value_seen_by_resolution, kValX);
}

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

    return MakeLogic4VecVal(a, 1, 0);
  };

  ResolveUserDefinedNetInit(net, nt, arena);
  EXPECT_EQ(ValOf(*var), kVal0);
}

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

TEST(NettypeInitialization, DefaultIsXNotZ) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  EXPECT_NE(ValOf(*var), kValZ);
  EXPECT_EQ(ValOf(*var), kValX);
}

TEST(NettypeInitialization, ResolutionOverwritesDefault) {
  Arena arena;
  auto* var = MakeVar(arena, 1);
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;

  EXPECT_EQ(ValOf(*var), kValX);

  UserNettypeInit nt;
  nt.resolution = [](Arena& a,
                     const std::vector<Logic4Vec>& ) -> Logic4Vec {
    return MakeLogic4VecVal(a, 1, 1);
  };

  ResolveUserDefinedNetInit(net, nt, arena);
  EXPECT_EQ(ValOf(*var), kVal1);
}
